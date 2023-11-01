{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PartialTypeSignatures #-}

-- Closure conversion

-- For now this file only contains the first step which consists of converting a
-- normal De Bruijn representation to one where lambdas explicitly store their
-- free variables.

module ClosConv (DB (..), Fun (..), closureConvert) where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Identity
import Data.Kind


-- DEFINITIONS


data Var env a where
  VZ :: Var (a : env) a
  VS :: Var env a -> Var (x : env) a

instance Show (Var env a) where
  show v0 = show (varToInt v0) where
    varToInt :: Var xs a -> Int
    varToInt VZ = 0
    varToInt (VS v) = 1 + varToInt v

data DB env a where
  Var :: Var env a -> DB env a
  Lam :: DB (a : env) b -> DB env (a -> b)
  App :: DB env (a -> b) -> DB env a -> DB env b

deriving instance Show (DB env a)


-- PART I - FREE VARIABLE ANALYSIS


data Sel env env' where
  Keep :: (KnownList env, KnownList env') => Sel env env' -> Sel (x : env) (x : env')
  Drop :: (KnownList env, KnownList env') => Sel env env' -> Sel (x : env) env'
  Done :: Sel '[] '[]

-- -- Normalising keep
-- pattern Keep :: forall env env'. forall x env'' env'''. (env' ~ (x : env'''), env ~ (x : env'')) => Sel env'' env''' -> Sel env env'
-- pattern Keep s <- Keep' s where
--   Keep KeepAll = KeepAll
--   Keep s = Keep' s
-- 
-- -- Normalising drop
-- pattern Drop :: forall env env'. forall x env''. (env ~ (x : env'')) => Sel env'' env' -> Sel env env'
-- pattern Drop s <- Drop' s where
--   Drop DropAll = DropAll
--   Drop s = Drop' s
-- 
-- {-# COMPLETE Keep, Drop, DropAll, KeepAll #-}

deriving instance Show (Sel env env')

data DB' env a where
  Var' :: Var env a -> DB' env a
  Lam' :: Sel env env' -> DB' (a : env') b -> DB' env (a -> b)
  App' :: DB' env (a -> b) -> DB' env a -> DB' env b

deriving instance Show (DB' env a)

type KnownList :: forall {k}. [k] -> Constraint 
class KnownList xs where
  listVal :: HList Proxy xs

instance KnownList '[] where
  listVal = HNil
instance KnownList xs => KnownList (x : xs) where
  listVal = HCons Proxy listVal

dropHList :: HList Proxy env -> Sel env '[]
dropHList HNil = Done
dropHList (HCons _ xs) = Drop (dropHList xs)

keepAll :: KnownList env => Sel env env
keepAll = go listVal where
  go :: HList Proxy env -> Sel env env
  go HNil = Done
  go (HCons _ xs) = Keep (go xs)

varSel :: forall env a. KnownList env => Var env a -> Sel env '[a]
varSel = go (listVal @env) where
  go :: HList Proxy env' -> Var env' a -> Sel env' '[a]
  go (HCons _ h) VZ = Keep (dropHList h) where
  go (HCons _ h) (VS v) = Drop (go h v)
  go HNil v = case v of {}

data ClosResult env a where
  ClosResult :: Sel env env' -> DB' env' a -> ClosResult env a

deriving instance Show (ClosResult env a)

data HList f xs where
  HCons :: KnownList xs => f x -> HList f xs -> HList f (x : xs)
  HNil :: HList f '[]

deriving instance (forall x. Show (f x)) => Show (HList f xs)

apSel :: Sel env env' -> Var env' a -> Var env a
apSel Done v = case v of {}
apSel (Drop s) v = VS (apSel s v)
apSel (Keep _) VZ = VZ
apSel (Keep s) (VS v) = VS (apSel s v)

withKnownSel :: Sel env env' -> ((KnownList env, KnownList env') => Sel env env' -> a) -> a
withKnownSel Done f = f Done
withKnownSel s@Keep{} f = f s
withKnownSel s@Drop{} f = f s

composeSel :: Sel env' env'' -> Sel env env' -> Sel env env''
composeSel Done s = s
composeSel s1 (Drop s2) = withKnownSel (composeSel s1 s2) Drop
composeSel (Keep s1) (Keep s2) = Keep (composeSel s1 s2)
composeSel (Drop s1) (Keep s2) = Drop (composeSel s1 s2)

weakenBy :: Sel env env' -> DB' env' a -> DB' env a
weakenBy s (Var' v) = Var' (apSel s v)
weakenBy s (App' x y) = App' (weakenBy s x) (weakenBy s y)
weakenBy s (Lam' s' x) = Lam' (composeSel s' s) x

close :: KnownList env => DB env a -> ClosResult env a
close (Var v) = ClosResult (varSel v) (Var' VZ)
close (Lam x) =
  case close x of
    ClosResult (Keep sx) x' -> ClosResult sx (Lam' keepAll x')
    ClosResult (Drop sx) x' -> ClosResult sx (Lam' keepAll (weakenBy (Drop keepAll) x'))
close (App x y) = case (close x, close y) of
  (ClosResult s1 x1, ClosResult s2 x2) ->
    case mergeSel s1 s2 of
      MergeResult s3 s1' s2' -> 
        ClosResult s3 (weakenBy s1' x1 `App'` weakenBy s2' x2)

data MergeResult env env1 env2 where
  MergeResult :: KnownList env3 => Sel env env3 -> Sel env3 env1 -> Sel env3 env2 -> MergeResult env env1 env2

mergeSel :: Sel env env1 -> Sel env env2 -> MergeResult env env1 env2
mergeSel Done Done = MergeResult Done Done Done
mergeSel (Drop s1) (Drop s2) = case mergeSel s1 s2 of MergeResult s' w1 w2 -> MergeResult (Drop s') w1 w2
mergeSel (Keep s1) (Drop s2) = case mergeSel s1 s2 of MergeResult s' w1 w2 -> MergeResult (Keep s') (Keep w1) (Drop w2)
mergeSel (Drop s1) (Keep s2) = case mergeSel s1 s2 of MergeResult s' w1 w2 -> MergeResult (Keep s') (Drop w1) (Keep w2)
mergeSel (Keep s1) (Keep s2) = case mergeSel s1 s2 of MergeResult s' w1 w2 -> MergeResult (Keep s') (Keep w1) (Keep w2)


-- PART II - LIFTING TO THE TOP LEVEL


type FunType :: [Type] -> Type -> Type -> Type
data FunType ctx a b

data Fun fun var a where
  Fn :: Fun fun var (HList Identity ctx) -> Var fun (FunType ctx a b) -> Fun fun var (a -> b)
  Vr :: Fun fun var var
  (:$) :: Fun fun var (a -> b) -> Fun fun var a -> Fun fun var b

  Tp :: HList (Fun fun var) xs -> Fun fun var (HList Identity xs)
  Pr :: Var xs a -> Fun fun var (HList Identity xs) -> Fun fun var a

deriving instance Show (Fun fun var a)

infixl 1 :$

data TopLevel fun a where
  TopLevel :: Fun fun (HList Identity (a : ctx)) b -> TopLevel fun (FunType ctx a b)

deriving instance Show (TopLevel fun a)

data ConvResult var a where
  ConvResult :: KnownList fun => HList (TopLevel fun) fun -> Fun fun var a -> ConvResult var a

deriving instance Show (ConvResult var a)

type (++) :: [k] -> [k] -> [k]
type family xs ++ ys where
  '[] ++ ys = ys
  (x : xs) ++ ys = x : (xs ++ ys)

assoc :: HList Proxy xs -> Proxy ys -> Proxy zs -> ((xs ++ ys) ++ zs :~: xs ++ (ys ++ zs))
assoc HNil Proxy Proxy = Refl
assoc (HCons Proxy h) p1 p2 = case assoc h p1 p2 of Refl -> Refl

rightId :: HList Proxy xs -> (xs ++ '[] :~: xs)
rightId HNil = Refl
rightId (HCons Proxy h) = case rightId h of Refl -> Refl

withKnownHList :: HList f xs -> (KnownList xs => HList f xs -> a) -> a
withKnownHList HNil f = f HNil
withKnownHList h@HCons{} f = f h

hAppend :: HList f xs -> HList f ys -> HList f (xs ++ ys)
hAppend HNil ys = ys
hAppend (HCons x xs) ys = withKnownHList (hAppend xs ys) (HCons x)

hSnoc :: HList f xs -> f x -> HList f (xs ++ '[x])
hSnoc h x = hAppend h (HCons x HNil)

weakenVar :: HList Proxy pre -> HList Proxy new -> Proxy env -> Var (pre ++ env) a -> Var (pre ++ (new ++ env)) a
weakenVar HCons {} _ _ VZ = VZ
weakenVar (HCons Proxy pre) new env (VS x) = VS (weakenVar pre new env x)
weakenVar HNil HNil _ x = x
weakenVar HNil (HCons Proxy new) env x = VS (weakenVar HNil new env x)

weakenFun :: HList Proxy pre -> HList Proxy new -> Proxy fun -> Fun (pre ++ fun) var a -> Fun (pre ++ (new ++ fun)) var a
weakenFun h1 h2 p3 = \case
  Fn ctx x -> Fn (weakenFun h1 h2 p3 ctx) (weakenVar h1 h2 p3 x)
  Vr -> Vr
  x :$ y -> weakenFun h1 h2 p3 x :$ weakenFun h1 h2 p3 y
  Tp x -> Tp (hmap (weakenFun h1 h2 p3) x)
  Pr v x -> Pr v (weakenFun h1 h2 p3 x)

weakenTopLevel :: HList Proxy pre -> HList Proxy new -> Proxy fun -> TopLevel (pre ++ fun) a -> TopLevel (pre ++ (new ++ fun)) a
weakenTopLevel p1 p2 p3 (TopLevel x) = TopLevel (weakenFun p1 p2 p3 x)

hmap :: (forall x. f x -> f' x) -> HList f xs -> HList f' xs
hmap _ HNil = HNil
hmap f (HCons x xs) = HCons (f x) (hmap f xs)

funSel :: Sel env env' -> Fun fun var (HList Identity env) -> Fun fun var (HList Identity env')
funSel s0 x0 = Tp (go HNil s0 x0) where

  hlistToVar :: Proxy zs -> HList f xs -> Var (xs ++ (y : zs)) y
  hlistToVar _ HNil = VZ
  hlistToVar p (HCons _ xs) = VS (hlistToVar p xs)

  go :: HList Proxy pre -> Sel env env' -> Fun fun var (HList Identity (pre ++ env)) -> HList (Fun fun var) env'
  go _ Done _ = HNil
  go pre (Drop @env @_ @x s) x = 
    case assoc pre (Proxy @'[x]) (Proxy @env) of 
      Refl -> go (hSnoc pre (Proxy @x)) s x
  go pre (Keep @env @_ @x s) x = 
    case assoc pre (Proxy @'[x]) (Proxy @env) of 
      Refl -> 
        HCons
          (Pr (hlistToVar (Proxy @env) pre) x)
          (go (hSnoc pre (Proxy @x)) s x)

conv :: DB' env a -> ConvResult (HList Identity env) a
conv (Var' v) = ConvResult HNil (Pr v Vr)
conv (Lam' s x) =
  case conv x of
    ConvResult h x' ->
      let h' = hmap (weakenTopLevel HNil (HCons Proxy HNil) Proxy) (HCons (TopLevel x') h) in
      ConvResult h' (Fn (funSel s Vr) VZ)
conv (App' x y) = 
  case conv x of
    ConvResult @funx hx x' ->
      case conv y of
        ConvResult @funy hy y' ->
          let hpx = hmap (const Proxy) hx
              hpy = hmap (const Proxy) hy
          in
          case (rightId (hmap (const Proxy) hx), rightId (hmap (const Proxy) hy)) of 
            (Refl, Refl) -> 
              withKnownHList
                (hAppend
                  (hmap (weakenTopLevel hpx hpy (Proxy @'[])) hx)
                  (hmap (weakenTopLevel HNil hpx (Proxy @funy)) hy)
                )
                (\h' ->
                  ConvResult  h'
                    (weakenFun hpx hpy (Proxy @'[]) x' :$ weakenFun HNil hpx (Proxy @funy) y')
                )

closureConvert :: DB '[] a -> ConvResult (HList Identity '[]) a
closureConvert x = 
  case close x of
    ClosResult Done y -> conv y

infixl `App`

pred =
--  \n f x ->
  Lam $ Lam $ Lam $
--    n                        (\g     h ->  h             (g                           f              ))       (\u ->  x         )       (\u -> u     )
    (Var $ VS $ VS $ VZ) `App` (Lam $ Lam $ (Var VZ) `App` ((Var $ VS VZ) `App` (Var $ VS $ VS $ VS VZ))) `App` (Lam (Var $ VS VZ)) `App` (Lam (Var VZ))

-- >>> close ClosConv.pred
-- ClosResult HNil Done (Lam' Done (Lam' (Keep Done) (Lam' (Keep (Keep Done)) (App' (App' (App' (Var' (VS (VS VZ))) (Lam' (Drop (Keep Done)) (Lam' (Keep (Keep Done)) (App' (Var' VZ) (App' (Var' (VS VZ)) (Var' (VS (VS VZ)))))))) (Lam' (Keep Done) (Var' (VS VZ)))) (Lam' Done (Var' VZ))))))


-- pred' :: DB' '[] ((((a1 -> a2) -> (a2 -> b1) -> b1) -> (a3 -> b2) -> (b3 -> b3) -> b4) -> a1 -> b2 -> b4)
-- pred' = Lam' Done (Lam' (Keep Done) (Lam' (Keep (Keep Done))
--   (App' (App' (App' (Var' (VS (VS VZ)))
--                     (Lam' (Drop (Keep Done)) (Lam' (Keep (Keep Done)) (App' (Var' VZ) (App' (Var' (VS VZ)) (Var' (VS (VS VZ))))))))
--               (Lam' (Keep Done) (Var' (VS VZ))))
--         (Lam' Done (Var' VZ)))))

-- Without Sel minimization:
--
-- pred' = (Lam' Done (Lam' (Keep Done) (Lam' (Keep (Keep Done))
--         (App' (App' (App' (Var' (VS (VS VZ)))
--                           (Lam' (Drop (Keep (Drop Done))) (Lam' (Keep (Keep Done)) (App' (Var' VZ) (App' (Var' (VS VZ)) (Var' (VS (VS VZ))))))))
--                     (Lam' (Keep (Drop (Drop Done))) (Var' (VS VZ))))
--               (Lam' (Drop (Drop (Drop Done))) (Var' VZ))))))

-- >>> conv pred'
-- ConvResult (HCons (TopLevel (Fn (Tp (HCons (Pr 0 Vr) HNil)) 1)) (HCons (TopLevel (Fn (Tp (HCons (Pr 0 Vr) (HCons (Pr 1 Vr) HNil))) 2)) (HCons (TopLevel (((Pr 2 Vr :$ Fn (Tp (HCons (Pr 1 Vr) HNil)) 3) :$ Fn (Tp (HCons (Pr 0 Vr) HNil)) 5) :$ Fn (Tp HNil) 6)) (HCons (TopLevel (Fn (Tp (HCons (Pr 0 Vr) (HCons (Pr 1 Vr) HNil))) 4)) (HCons (TopLevel (Pr 0 Vr :$ (Pr 1 Vr :$ Pr 2 Vr))) (HCons (TopLevel (Pr 1 Vr)) (HCons (TopLevel (Pr 0 Vr)) HNil))))))) (Fn (Tp HNil) 0)

-- ConvResult
--   0 (TopLevel (Fn (Pr 0 Vr) 1))                      \{}    n -> f1{n}
--   1 (TopLevel (Fn (Pr 0 Vr, Pr 1 Vr) 2))             \{n}   f -> f2{n f}
--   2 (TopLevel                                        \{n f} x -> n f3{f} f5{x} f6{}
--        (Pr 2 Vr :$ Fn (Pr 1 Vr) 3
--                 :$ Fn (Pr 0 Vr) 5
--                 :$ Fn () 6
--        )
--     )
--   3 (TopLevel (Fn (Pr 0 Vr, Pr 1 Vr) 4))             \{f}   g -> f4{g f}
--   4 (TopLevel (Pr 0 Vr :$ (Pr 1 Vr :$ Pr 2 Vr)))     \{g f} h -> h (g f)
--   5 (TopLevel (Pr 1 Vr))                             \{x}   u -> x
--   6 (TopLevel (Pr 0 Vr))                             \{}    u -> u
--   (Fn () 0)
