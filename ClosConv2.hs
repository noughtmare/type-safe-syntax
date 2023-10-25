{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}

-- Closure conversion

module ClosConv2 (DB (..), closureConvert) where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Identity
import Data.Kind

data Var env a where
  VZ :: Var (a : env) a
  VS :: Var env a -> Var (x : env) a

instance Show (Var env a) where
  show v = show (varToInt v)

varToInt :: Var xs a -> Int
varToInt VZ = 0
varToInt (VS v) = 1 + varToInt v

data DB env a where
  Var :: Var env a -> DB env a
  Lam :: DB (a : env) b -> DB env (a -> b)
  App :: DB env (a -> b) -> DB env a -> DB env b
  Tup :: HList (DB env) xs -> DB env (HList Identity xs)
  Prj :: Var xs a -> DB env (HList Identity xs) -> DB env a

deriving instance Show (DB env a)

data Sel env env' where
  Keep :: Sel env env' -> Sel (x : env) (x : env')
  Drop :: Sel env env' -> Sel (x : env) env'
  Done :: Sel env '[]

deriving instance Show (Sel env env')

varSel :: Var env a -> Sel env '[a]
varSel VZ = Keep Done
varSel (VS v) = Drop (varSel v)

type ClosResult :: ([k1] -> k2 -> Type) -> [k1] -> k2 -> Type
data ClosResult f env a where
  ClosResult :: Sel env env' -> f env' a -> ClosResult f env a

deriving instance (forall env'. Show (f env' a)) => Show (ClosResult f env a)

data HList f xs where
  HCons :: f x -> HList f xs -> HList f (x : xs)
  HNil :: HList f '[]

deriving instance (forall x. Show (f x)) => Show (HList f xs)

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

hAppend :: HList f xs -> HList f ys -> HList f (xs ++ ys)
hAppend HNil ys = ys
hAppend (HCons x xs) ys = HCons x (hAppend xs ys)

hSnoc :: HList f xs -> f x -> HList f (xs ++ '[x])
hSnoc h x = hAppend h (HCons x HNil)

weaken :: forall x env a. DB env a -> DB (x : env) a
weaken = weakenUnder HNil (HCons Proxy HNil) Proxy

weakenVar :: HList Proxy pre -> HList Proxy new -> Proxy env -> Var (pre ++ env) a -> Var (pre ++ (new ++ env)) a
weakenVar HCons {} _ _ VZ = VZ
weakenVar (HCons Proxy pre) new env (VS x) = VS (weakenVar pre new env x)
weakenVar HNil HNil _ x = x
weakenVar HNil (HCons Proxy new) env x = VS (weakenVar HNil new env x)

weakenUnder :: HList Proxy pre -> HList Proxy new -> Proxy env -> DB (pre ++ env) a -> DB (pre ++ (new ++ env)) a
weakenUnder pre new env (Var v) = Var (weakenVar pre new env v)
weakenUnder pre new env (App x y) = App (weakenUnder pre new env x) (weakenUnder pre new env y)
weakenUnder pre new env (Lam @a x) = Lam (weakenUnder (HCons (Proxy @a) pre) new env x)
weakenUnder pre new env (Tup xs) = Tup (hmap (weakenUnder pre new env) xs)
weakenUnder pre new env (Prj v x) = Prj v (weakenUnder pre new env x)

idSel :: Sel env' env -> Sel env env
idSel Done = Done
idSel (Keep h) = Keep (idSel h)
idSel (Drop h) = idSel h

close :: DB env a -> ClosResult DB env a
close (Var v) = ClosResult (varSel v) (Var VZ)
close (Lam x) = mapClosResult (\(DBUnder x') -> Lam x') $ closeUnder x
--  case close x of
--    ClosResult (Keep sx) x' -> ClosResult sx (Lam x')
--    ClosResult (Drop sx) x' -> ClosResult sx (Lam (weaken x'))
--    ClosResult Done x' -> ClosResult Done (Lam (weaken x'))
close (App x y) = 
  mapClosResult (\(HListDB (HCons x' (HCons y' HNil))) -> App x' y') $
    closeCombine (HCons (close x) (HCons (close y) HNil))
close (Tup xs) =
  mapClosResult (\(HListDB x) -> Tup x) $ closeCombine (hmap close xs)
close (Prj v x) = mapClosResult (Prj v) (close x)

data DBUnder x env a = DBUnder (DB (x : env) a)

closeUnder :: DB (x : env) a -> ClosResult (DBUnder x) env a
closeUnder x =
  case close x of
    ClosResult (Keep sx) x' -> ClosResult sx (DBUnder x')
    ClosResult (Drop sx) x' -> ClosResult sx (DBUnder (weaken x'))
    ClosResult Done x' -> ClosResult Done (DBUnder (weaken x'))

mapClosResult :: (forall env'. f env' a -> g env' b) -> ClosResult f env a -> ClosResult g env b
mapClosResult f (ClosResult s x) = ClosResult s (f x)

newtype HListDB env xs where
  HListDB :: HList (DB env) xs -> HListDB env xs

weakenVarBy :: Sel env env' -> Var env' a -> Var env a
weakenVarBy Done v = case v of {}
weakenVarBy (Keep _) VZ = VZ
weakenVarBy (Keep s) (VS v) = VS (weakenVarBy s v)
weakenVarBy (Drop s) v = VS (weakenVarBy s v)

weakenUnderBy :: Proxy pre -> Proxy env -> Proxy env' -> Sel (pre ++ env) (pre ++ env') -> DB (pre ++ env') a -> DB (pre ++ env) a
weakenUnderBy _ _ _ s (Var v) = Var (weakenVarBy s v)
weakenUnderBy p1 p2 p3 s (App x y) = App (weakenUnderBy p1 p2 p3 s x) (weakenUnderBy p1 p2 p3 s y)
weakenUnderBy p1 p2 p3 s (Tup xs) = Tup (hmap (weakenUnderBy p1 p2 p3 s) xs)
weakenUnderBy p1 p2 p3 s (Prj v x) = Prj v (weakenUnderBy p1 p2 p3 s x)
weakenUnderBy (Proxy @pre) p2 p3 s (Lam x) = Lam (weakenUnderBy (Proxy @(_ : pre)) p2 p3 (Keep s) x)

weakenBy :: Sel env env' -> DB env' a -> DB env a
weakenBy = weakenUnderBy (Proxy @'[]) Proxy Proxy

data MergeResult env env1 env2 where
  MergeResult :: 
    Sel env env3 ->
    Sel env3 env1 ->
    Sel env3 env2 -> 
    MergeResult env env1 env2

mergeSel :: Sel env env1 -> Sel env env2 -> MergeResult env env1 env2
mergeSel Done s2 = MergeResult s2 Done (idSel s2)
mergeSel s1 Done = MergeResult s1 (idSel s1) Done
mergeSel (Drop s1) (Drop s2) =
  case mergeSel s1 s2 of
    MergeResult s' w1 w2 -> MergeResult (Drop s') w1 w2
mergeSel (Keep s1) (Drop s2) =
  case mergeSel s1 s2 of
    MergeResult s' w1 w2 -> MergeResult (Keep s') (Keep w1) (Drop w2)
mergeSel (Drop s1) (Keep s2) =
  case mergeSel s1 s2 of
    MergeResult s' w1 w2 -> MergeResult (Keep s') (Drop w1) (Keep w2)
mergeSel (Keep s1) (Keep s2) =
  case mergeSel s1 s2 of
    MergeResult s' w1 w2 -> MergeResult (Keep s') (Keep w1) (Keep w2)

closeCombine :: HList (ClosResult DB env) as -> ClosResult HListDB env as
closeCombine HNil = ClosResult Done (HListDB HNil)
closeCombine (HCons (ClosResult s x) xs) =
  case closeCombine xs of
    ClosResult ss (HListDB ys) -> 
      case mergeSel s ss of
        MergeResult s' s1 s2 -> 
          ClosResult s' (HListDB (HCons (weakenBy s1 x) (hmap (weakenBy s2) ys)))

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

type ConvResult :: ([Type] -> Type -> k -> Type) -> Type -> k -> Type
data ConvResult f var a where
  ConvResult :: HList (TopLevel fun) fun -> f fun var a -> ConvResult f var a

deriving instance (forall fun. Show (f fun var a)) => Show (ConvResult f var a)

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
  hlistToVar :: HList f xs -> Proxy zs -> Var (xs ++ (y : zs)) y
  hlistToVar HNil _ = VZ
  hlistToVar (HCons _ xs) p = VS (hlistToVar xs p)

  go :: HList Proxy pre -> Sel env env' -> Fun fun var (HList Identity (pre ++ env)) -> HList (Fun fun var) env'
  go _ Done _ = HNil
  go pre (Drop @env @_ @x s) x =
    case assoc pre (Proxy @'[x]) (Proxy @env) of 
      Refl -> go (hSnoc pre (Proxy @x)) s x
  go pre (Keep @env @_ @x s) x = 
    case assoc pre (Proxy @'[x]) (Proxy @env) of
      Refl -> 
        HCons
          (Pr (hlistToVar pre (Proxy @env)) x)
          (go (hSnoc pre (Proxy @x)) s x)

hProxy :: HList f xs -> Proxy xs
hProxy _ = Proxy

newtype HListFun fun var a = HListFun (HList (Fun fun var) a)

convCombine :: HList (ConvResult Fun var) a -> ConvResult HListFun var a
convCombine HNil = ConvResult HNil (HListFun HNil)
convCombine (HCons (ConvResult @fun1 h1 x) xs) =
  case convCombine xs of
    ConvResult @fun2 h2 (HListFun xs') -> 
      let
        hp1 = hmap (const Proxy) h1
        hp2 = hmap (const Proxy) h2
      in
      case (rightId hp1, rightId hp2) of
        (Refl, Refl) ->
          let h1' = hmap (weakenTopLevel hp1 hp2 (Proxy @'[])) h1
              h2' = hmap (weakenTopLevel HNil hp1 (hProxy hp2)) h2 in
          ConvResult 
            @(fun1 ++ fun2)
            (hAppend h1' h2')
            (HListFun 
              (HCons 
                (weakenFun hp1 hp2 (Proxy @'[]) x) 
                (hmap (weakenFun HNil hp1 (hProxy hp2)) xs')))

mapConvResult :: (forall fun. f fun var a -> g fun var b) -> ConvResult f var a -> ConvResult g var b
mapConvResult f (ConvResult h x) = ConvResult h (f x)

conv :: DB env a -> ConvResult Fun (HList Identity env) a
conv (Var v) = ConvResult HNil (Pr v Vr)
conv (Lam x0) = 
  case closeUnder x0 of
    ClosResult s (DBUnder x) ->
      case conv x of
        ConvResult h x' ->
          let h' = hmap (weakenTopLevel HNil (HCons Proxy HNil) Proxy) (HCons (TopLevel x') h) in
          ConvResult h' (Fn (funSel s Vr) VZ)
conv (App x y) = 
  mapConvResult (\(HListFun (HCons x' (HCons y' HNil))) -> x' :$ y') $
    convCombine $ hmap conv (HCons x (HCons y HNil))
conv (Tup xs) = mapConvResult (\(HListFun xs') -> Tp xs') $ convCombine (hmap conv xs)
conv (Prj v x) = mapConvResult (Pr v) (conv x)

closureConvert :: DB '[] a -> ConvResult Fun (HList Identity '[]) a
closureConvert x = case close x of ClosResult Done y -> conv y

infixl `App`

pred =
--  \n f x ->
  Lam $ Lam $ Lam $
--    n                        (\g     h ->  h             (g                           f              ))       (\u ->  x         )       (\u -> u     )
    (Var $ VS $ VS $ VZ) `App` (Lam $ Lam $ (Var VZ) `App` ((Var $ VS VZ) `App` (Var $ VS $ VS $ VS VZ))) `App` (Lam (Var $ VS VZ)) `App` (Lam (Var VZ))

-- >>> closureConvert ClosConv2.pred
-- ConvResult (HCons (TopLevel (Fn (Tp (HCons (Pr 0 Vr) HNil)) 1)) (HCons (TopLevel (Fn (Tp (HCons (Pr 0 Vr) (HCons (Pr 1 Vr) HNil))) 2)) (HCons (TopLevel (((Pr 2 Vr :$ Fn (Tp (HCons (Pr 1 Vr) HNil)) 3) :$ Fn (Tp (HCons (Pr 0 Vr) HNil)) 5) :$ Fn (Tp HNil) 6)) (HCons (TopLevel (Fn (Tp (HCons (Pr 0 Vr) (HCons (Pr 1 Vr) HNil))) 4)) (HCons (TopLevel (Pr 0 Vr :$ (Pr 1 Vr :$ Pr 2 Vr))) (HCons (TopLevel (Pr 1 Vr)) (HCons (TopLevel (Pr 0 Vr)) HNil))))))) (Fn (Tp HNil) 0)


-- pred' :: DB' '[] ((((a1 -> a2) -> (a2 -> b1) -> b1) -> (a3 -> b2) -> (b3 -> b3) -> b4) -> a1 -> b2 -> b4)
-- pred' = Lam' Done (Lam' (Keep Done) (Lam' (Keep (Keep Done))
--   (App' (App' (App' (Var' (VS (VS VZ)))
--                     (Lam' (Drop (Keep Done)) (Lam' (Keep (Keep Done)) (App' (Var' VZ) (App' (Var' (VS VZ)) (Var' (VS (VS VZ))))))))
--               (Lam' (Keep Done) (Var' (VS VZ))))
--         (Lam' Done (Var' VZ)))))
-- 
-- -- Without Sel minimization:
-- --
-- -- pred' = (Lam' Done (Lam' (Keep Done) (Lam' (Keep (Keep Done))
-- --         (App' (App' (App' (Var' (VS (VS VZ)))
-- --                           (Lam' (Drop (Keep (Drop Done))) (Lam' (Keep (Keep Done)) (App' (Var' VZ) (App' (Var' (VS VZ)) (Var' (VS (VS VZ))))))))
-- --                     (Lam' (Keep (Drop (Drop Done))) (Var' (VS VZ))))
-- --               (Lam' (Drop (Drop (Drop Done))) (Var' VZ))))))
-- 
-- -- >>> conv pred'
-- -- ConvResult (HCons (TopLevel (Fn (Tp (HCons (Pr 0 Vr) HNil)) 1)) (HCons (TopLevel (Fn (Tp (HCons (Pr 0 Vr) (HCons (Pr 1 Vr) HNil))) 2)) (HCons (TopLevel (((Pr 2 Vr :$ Fn (Tp (HCons (Pr 1 Vr) HNil)) 3) :$ Fn (Tp (HCons (Pr 0 Vr) HNil)) 5) :$ Fn (Tp HNil) 6)) (HCons (TopLevel (Fn (Tp (HCons (Pr 0 Vr) (HCons (Pr 1 Vr) HNil))) 4)) (HCons (TopLevel (Pr 0 Vr :$ (Pr 1 Vr :$ Pr 2 Vr))) (HCons (TopLevel (Pr 1 Vr)) (HCons (TopLevel (Pr 0 Vr)) HNil))))))) (Fn (Tp HNil) 0)
-- 
-- -- ConvResult
-- --   0 (TopLevel (Fn (Pr 0 Vr) 1))                      \{}    n -> f1{n}
-- --   1 (TopLevel (Fn (Pr 0 Vr, Pr 1 Vr) 2))             \{n}   f -> f2{n f}
-- --   2 (TopLevel                                        \{n f} x -> n f3{f} f5{x} f6{}
-- --        (Pr 2 Vr :$ Fn (Pr 1 Vr) 3
-- --                 :$ Fn (Pr 0 Vr) 5
-- --                 :$ Fn () 6
-- --        )
-- --     )
-- --   3 (TopLevel (Fn (Pr 0 Vr, Pr 1 Vr) 4))             \{f}   g -> f4{g f}
-- --   4 (TopLevel (Pr 0 Vr :$ (Pr 1 Vr :$ Pr 2 Vr)))     \{g f} h -> h (g f)
-- --   5 (TopLevel (Pr 1 Vr))                             \{x}   u -> x
-- --   6 (TopLevel (Pr 0 Vr))                             \{}    u -> u
-- --   (Fn () 0)
-- 
-- -- let f6 = \{}    -> \u -> u
-- -- let f5 = \{x}   -> \u -> x
-- -- let f4 = \{g,f} -> \h -> h (g f)
-- -- let f3 = \{f}   -> \g -> f4{g,f}
-- -- let f2 = \{n,f} -> \x -> n f3{f} f5{x} f6{}
-- -- let f1 = \{n}   -> \f -> f2{n,f}
-- -- let f0 = \{}    -> \n -> f1{n}
-- -- f0
-- 
-- -- let f6 = \_ -> \u -> u
-- -- let f5 = \p -> \u -> p[0]
-- -- let f4 = \p -> \h -> h (p[0] p[1])
-- -- let f3 = \p -> \g -> f4 (g,p[0])
-- -- let f2 = \p -> \x -> p[0] (f3 p[1]) (f5 (x)) (f6 ())
-- -- let f1 = \p -> \f -> f2 (p[0],f)
-- -- let f0 = \_ -> \n -> f1 (n)
-- -- f0
