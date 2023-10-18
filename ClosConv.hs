{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}

-- Closure conversion

-- For now this file only contains the first step which consists of converting a
-- normal De Bruijn representation to one where lambdas explicitly store their
-- free variables.

module ClosConv (DB (..), DB' (..), close, Fun (..), conv) where

import Data.Proxy
import Data.Type.Equality

data Var env a where
  VZ :: Var (a : env) a
  VS :: Var env a -> Var (x : env) a

deriving instance Show (Var env a)

data DB env a where
  Var :: Var env a -> DB env a
  Lam :: DB (a : env) b -> DB env (a -> b)
  App :: DB env (a -> b) -> DB env a -> DB env b

deriving instance Show (DB env a)

data Sel env env' where
  Keep :: Sel env env' -> Sel (x : env) (x : env')
  Drop :: Sel env env' -> Sel (x : env) env'
  Done :: Sel env '[]

deriving instance Show (Sel env env')

data DB' env a where
  Var' :: Var env a -> DB' env a
  Lam' :: Sel env env' -> DB' (a : env') b -> DB' env (a -> b)
  App' :: DB' env (a -> b) -> DB' env a -> DB' env b

deriving instance Show (DB' env a)

varSel :: Var env a -> Sel env '[a]
varSel VZ = Keep Done
varSel (VS v) = Drop (varSel v)

data ClosResult pre env a where
  ClosResult :: HList Proxy env' -> Sel env env' -> DB' (pre ++ env') a -> ClosResult pre env a

deriving instance Show (ClosResult pre env a)

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

weaken' :: DB' env a -> DB' (x : env) a
weaken' = weakenUnder' HNil (HCons Proxy HNil) Proxy

weakenVar :: HList Proxy pre -> HList Proxy new -> Proxy env -> Var (pre ++ env) a -> Var (pre ++ (new ++ env)) a
weakenVar HCons {} _ _ VZ = VZ
weakenVar (HCons Proxy pre) new env (VS x) = VS (weakenVar pre new env x)
weakenVar HNil HNil _ x = x
weakenVar HNil (HCons Proxy new) env x = VS (weakenVar HNil new env x)

weakenUnderSel :: HList Proxy pre -> HList Proxy new -> Proxy env -> Sel (pre ++ env) env' -> Sel (pre ++ (new ++ env)) env'
weakenUnderSel HCons {} _ _ Done = Done
weakenUnderSel (HCons Proxy pre) new env (Keep s) = Keep (weakenUnderSel pre new env s)
weakenUnderSel (HCons Proxy pre) new env (Drop s) = Drop (weakenUnderSel pre new env s)
weakenUnderSel HNil HNil _ x = x
weakenUnderSel HNil (HCons Proxy new) env x = Drop (weakenUnderSel HNil new env x)

weakenUnder' :: HList Proxy pre -> HList Proxy new -> Proxy env -> DB' (pre ++ env) a -> DB' (pre ++ (new ++ env)) a
weakenUnder' pre new env (Var' v) = Var' (weakenVar pre new env v)
weakenUnder' pre new env (App' x y) = App' (weakenUnder' pre new env x) (weakenUnder' pre new env y)
weakenUnder' pre new env (Lam' s x) = Lam' (minimize (weakenUnderSel pre new env s)) x

minimize :: Sel env env' -> Sel env env'
minimize (Drop x) =
  case minimize x of
    Done -> Done
    x' -> Drop x'
minimize (Keep x) = Keep (minimize x)
minimize Done = Done

idSel :: HList Proxy env -> Sel env env
idSel HNil = Done
idSel (HCons Proxy h) = Keep (idSel h)

close :: DB env a -> ClosResult '[] env a
close (Var v) = ClosResult (HCons Proxy HNil) (varSel v) (Var' VZ)
close (Lam x) =
  case close x of
    ClosResult (HCons Proxy h) (Keep sx) x' -> ClosResult h sx (Lam' (idSel h) x')
    ClosResult h (Drop sx) x' -> ClosResult h sx (Lam' (idSel h) (weaken' x'))
    ClosResult HNil Done x' -> ClosResult HNil Done (Lam' Done (weaken' x'))
close (App x y) = closeApp HNil (close x) (close y)

closeApp :: HList Proxy pre -> ClosResult pre env (a -> b) -> ClosResult pre env a -> ClosResult pre env b
closeApp pre (ClosResult hx (Drop sx) x) (ClosResult hy (Drop sy) y) =
  case closeApp pre (ClosResult hx sx x) (ClosResult hy sy y) of
    ClosResult hz sz z -> ClosResult hz (Drop sz) z
closeApp pre (ClosResult (HCons @_ @x @xs Proxy hx) (Keep sx) x) (ClosResult (HCons @_ @_ @ys Proxy hy) (Keep sy) y) =
  case (assoc pre (Proxy @'[x]) (Proxy @xs), assoc pre (Proxy @'[x]) (Proxy @ys)) of
    (Refl, Refl) ->
      case closeApp (hAppend pre (HCons (Proxy @x) HNil)) (ClosResult hx sx x) (ClosResult hy sy y) of
        ClosResult @env' hz sz z ->
          case assoc pre (Proxy @'[x]) (Proxy @env') of
            Refl -> ClosResult (HCons (Proxy @x) hz) (Keep sz) z
closeApp pre (ClosResult (HCons @_ @x @xs Proxy hx) (Keep sx) x) (ClosResult @ys hy (Drop sy) y) =
  case (assoc pre (Proxy @'[x]) (Proxy @xs), assoc pre (Proxy @'[x]) (Proxy @ys)) of
    (Refl, Refl) ->
      case closeApp
        (hAppend pre (HCons (Proxy @x) HNil))
        (ClosResult hx sx x)
        (ClosResult hy sy (weakenUnder' pre (HCons (Proxy @x) HNil) (Proxy @ys) y)) of
        ClosResult @env' hz sz z ->
          case assoc pre (Proxy @'[x]) (Proxy @env') of
            Refl -> ClosResult (HCons (Proxy @x) hz) (Keep sz) z
closeApp pre (ClosResult @xs hx (Drop sx) x) (ClosResult (HCons @_ @y @ys Proxy hy) (Keep sy) y) =
  case (assoc pre (Proxy @'[y]) (Proxy @xs), assoc pre (Proxy @'[y]) (Proxy @ys)) of
    (Refl, Refl) ->
      case closeApp
        (hAppend pre (HCons (Proxy @y) HNil))
        (ClosResult hx sx (weakenUnder' pre (HCons (Proxy @y) HNil) (Proxy @xs) x))
        (ClosResult hy sy y) of
        ClosResult @env' hz sz z ->
          case assoc pre (Proxy @'[y]) (Proxy @env') of
            Refl -> ClosResult (HCons (Proxy @y) hz) (Keep sz) z
closeApp pre (ClosResult HNil Done x) (ClosResult hy sy y) =
  case rightId hy of
    Refl ->
      ClosResult hy sy (App' (weakenUnder' pre hy (Proxy @'[]) x) y)
closeApp pre (ClosResult hx sx x) (ClosResult HNil Done y) =
  case rightId hx of
    Refl ->
      ClosResult hx sx (App' x (weakenUnder' pre hx (Proxy @'[]) y))

data Fun fun var a where
  Fn :: Fun fun var ctx -> Var fun ((a,ctx) -> b) -> Fun fun var (a -> b)
  Vr :: Fun fun var var
  Ap :: Fun fun var (a -> b) -> Fun fun var a -> Fun fun var b

  Tp :: Fun fun var a -> Fun fun var b -> Fun fun var (a, b)
  P1 :: Fun fun var ((a, b) -> a)
  P2 :: Fun fun var ((a, b) -> b)
  U  :: Fun fun var ()

deriving instance Show (Fun fun var a)

data TopLevel fun a where
  TopLevel :: Fun fun var b -> TopLevel fun (var -> b)

deriving instance Show (TopLevel fun a)

lookupHList :: Var env a -> HList f env -> f a
lookupHList VZ (HCons x _) = x
lookupHList (VS v) (HCons _ xs) = lookupHList v xs

selectHList :: Sel env env' -> HList f env -> HList f env'
selectHList Done _ = HNil
selectHList (Keep s) (HCons x xs) = HCons x (selectHList s xs)
selectHList (Drop s) (HCons _ xs) = selectHList s xs

type family Unroll xs where
  Unroll '[] = ()
  Unroll (x : xs) = (x, Unroll xs)

pVar :: HList Proxy pre -> Var env b -> Fun fun (Unroll (pre ++ env)) (Unroll env) -> Fun fun (Unroll (pre ++ env)) b 
pVar _ VZ x = Ap P1 x
pVar h (VS @env' @_ @x v) x = 
  case assoc h (Proxy @'[x]) (Proxy @env') of 
    Refl ->
      pVar (hAppend h (HCons (Proxy @x) HNil)) v (Ap P2 x)

data ConvResult var a where
  ConvResult :: HList (TopLevel fun) fun -> Fun fun var a -> ConvResult var a

deriving instance Show (ConvResult var a)

weakenFun :: HList Proxy pre -> HList Proxy new -> Proxy fun -> Fun (pre ++ fun) var a -> Fun (pre ++ (new ++ fun)) var a
weakenFun h1 h2 p3 = \case
  Fn ctx x -> Fn (weakenFun h1 h2 p3 ctx) (weakenVar h1 h2 p3 x)
  Vr -> Vr
  Ap x y -> Ap (weakenFun h1 h2 p3 x) (weakenFun h1 h2 p3 y)
  Tp x y -> Tp (weakenFun h1 h2 p3 x) (weakenFun h1 h2 p3 y)
  P1 -> P1
  P2 -> P2
  U -> U

weakenTopLevel :: HList Proxy pre -> HList Proxy new -> Proxy fun -> TopLevel (pre ++ fun) a -> TopLevel (pre ++ (new ++ fun)) a
weakenTopLevel p1 p2 p3 (TopLevel x) = TopLevel (weakenFun p1 p2 p3 x)

hmap :: (forall x. f x -> f' x) -> HList f xs -> HList f' xs
hmap _ HNil = HNil
hmap f (HCons x xs) = HCons (f x) (hmap f xs)

unselect :: Sel env env' -> Var env' a -> Var env a
unselect (Drop s) v = VS (unselect s v)
unselect (Keep s) (VS v) = VS (unselect s v)
unselect Keep{} VZ = VZ
unselect Done v = case v of {}

funVar :: Var env a -> Fun fun var (Unroll env) -> Fun fun var a
funVar VZ x = Ap P1 x
funVar (VS v) x = funVar v (Ap P2 x)

funSel :: Sel env env' -> Fun fun var (Unroll env) -> Fun fun var (Unroll env')
funSel Done _ = U
funSel (Keep s) x = Tp (Ap P1 x) (funSel s (Ap P2 x))
funSel (Drop s) x = funSel s (Ap P2 x)

conv :: DB' env a -> ConvResult (Unroll env) a
conv (Var' v) = ConvResult HNil (funVar v Vr)
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
              ConvResult 
                (hAppend
                  (hmap (weakenTopLevel hpx hpy (Proxy @'[])) hx)
                  (hmap (weakenTopLevel HNil hpx (Proxy @funy)) hy)
                )
                (Ap
                  (weakenFun hpx hpy (Proxy @'[]) x') 
                  (weakenFun HNil hpx (Proxy @funy) y')
                )


infixl `App`

pred =
--  \n f x ->
  Lam $ Lam $ Lam $
--    n                        (\g     h ->  h             (g                           f              ))       (\u ->  x         )       (\u -> u     )
    (Var $ VS $ VS $ VZ) `App` (Lam $ Lam $ (Var VZ) `App` ((Var $ VS VZ) `App` (Var $ VS $ VS $ VS VZ))) `App` (Lam (Var $ VS VZ)) `App` (Lam (Var VZ))

-- >>> close ClosConv.pred
-- ClosResult HNil Done (Lam' Done (Lam' (Keep Done) (Lam' (Keep (Keep Done)) (App' (App' (App' (Var' (VS (VS VZ))) (Lam' (Drop (Keep Done)) (Lam' (Keep (Keep Done)) (App' (Var' VZ) (App' (Var' (VS VZ)) (Var' (VS (VS VZ)))))))) (Lam' (Keep Done) (Var' (VS VZ)))) (Lam' Done (Var' VZ))))))


pred' :: DB' '[] ((((a1 -> a2) -> (a2 -> b1) -> b1)     -> (a3 -> b2) -> (b3 -> b3) -> b4)    -> a1 -> b2 -> b4)
pred' = Lam' Done (Lam' (Keep Done) (Lam' (Keep (Keep Done))
  (App' (App' (App' (Var' (VS (VS VZ)))
                    (Lam' (Drop (Keep Done)) (Lam' (Keep (Keep Done)) (App' (Var' VZ) (App' (Var' (VS VZ)) (Var' (VS (VS VZ))))))))
              (Lam' (Keep Done) (Var' (VS VZ))))
        (Lam' Done (Var' VZ)))))

-- without minimization:
--
-- pred' = (Lam' Done (Lam' (Keep Done) (Lam' (Keep (Keep Done))
--         (App' (App' (App' (Var' (VS (VS VZ)))
--                           (Lam' (Drop (Keep (Drop Done))) (Lam' (Keep (Keep Done)) (App' (Var' VZ) (App' (Var' (VS VZ)) (Var' (VS (VS VZ))))))))
--                     (Lam' (Keep (Drop (Drop Done))) (Var' (VS VZ))))
--               (Lam' (Drop (Drop (Drop Done))) (Var' VZ))))))

-- >>> conv pred'
-- ConvResult (HCons (TopLevel (Fn (Tp (Ap P1 Vr) U) (VS VZ))) (HCons (TopLevel (Fn (Tp (Ap P1 Vr) (Tp (Ap P1 (Ap P2 Vr)) U)) (VS (VS VZ)))) (HCons (TopLevel (Ap (Ap (Ap (Ap P1 (Ap P2 (Ap P2 Vr))) (Fn (Tp (Ap P1 (Ap P2 Vr)) U) (VS (VS (VS VZ))))) (Fn (Tp (Ap P1 Vr) U) (VS (VS (VS (VS (VS VZ))))))) (Fn U (VS (VS (VS (VS (VS (VS VZ))))))))) (HCons (TopLevel (Fn (Tp (Ap P1 Vr) (Tp (Ap P1 (Ap P2 Vr)) U)) (VS (VS (VS (VS VZ)))))) (HCons (TopLevel (Ap (Ap P1 Vr) (Ap (Ap P1 (Ap P2 Vr)) (Ap P1 (Ap P2 (Ap P2 Vr)))))) (HCons (TopLevel (Ap P1 (Ap P2 Vr))) (HCons (TopLevel (Ap P1 Vr)) HNil))))))) (Fn U VZ)
