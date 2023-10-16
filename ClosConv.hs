{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

-- Closure conversion

-- For now this file only contains the first step which consists of converting a
-- normal De Bruijn representation to one where lambdas explicitly store their
-- free variables.

module ClosConv (close) where

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

weakenUnderVar :: HList Proxy pre -> HList Proxy new -> Proxy env -> Var (pre ++ env) a -> Var (pre ++ (new ++ env)) a
weakenUnderVar HCons {} _ _ VZ = VZ
weakenUnderVar (HCons Proxy pre) new env (VS x) = VS (weakenUnderVar pre new env x)
weakenUnderVar HNil HNil _ x = x
weakenUnderVar HNil (HCons Proxy new) env x = VS (weakenUnderVar HNil new env x)

weakenUnderSel :: HList Proxy pre -> HList Proxy new -> Proxy env -> Sel (pre ++ env) env' -> Sel (pre ++ (new ++ env)) env'
weakenUnderSel HCons {} _ _ Done = Done
weakenUnderSel (HCons Proxy pre) new env (Keep s) = Keep (weakenUnderSel pre new env s)
weakenUnderSel (HCons Proxy pre) new env (Drop s) = Drop (weakenUnderSel pre new env s)
weakenUnderSel HNil HNil _ x = x
weakenUnderSel HNil (HCons Proxy new) env x = Drop (weakenUnderSel HNil new env x)

weakenUnder' :: HList Proxy pre -> HList Proxy new -> Proxy env -> DB' (pre ++ env) a -> DB' (pre ++ (new ++ env)) a
weakenUnder' pre new env (Var' v) = Var' (weakenUnderVar pre new env v)
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

-- data Fun env a b where
--   Glo :: _ env a b -> Fun env a b
--   Id :: Fun env a a
--   Compose :: Fun env b c -> Fun env a b -> Fun env a c
--
-- conv :: ClosResult '[] '[] a -> (HList _ g, Var g a)
-- conv = _

infixl `App`

pred =
--  \n f x ->
  Lam $ Lam $ Lam $
--    n                        (\g     h ->  h             (g                           f              ))       (\u ->  x         )       (\u -> u     )
    (Var $ VS $ VS $ VZ) `App` (Lam $ Lam $ (Var VZ) `App` ((Var $ VS VZ) `App` (Var $ VS $ VS $ VS VZ))) `App` (Lam (Var $ VS VZ)) `App` (Lam (Var VZ))

-- >>> close ClosConv.pred
-- ClosResult HNil Done (Lam' Done (Lam' (Keep Done) (Lam' (Keep (Keep Done)) (App' (App' (App' (Var' (VS (VS VZ))) (Lam' (Drop (Keep Done)) (Lam' (Keep (Keep Done)) (App' (Var' VZ) (App' (Var' (VS VZ)) (Var' (VS (VS VZ)))))))) (Lam' (Keep Done) (Var' (VS VZ)))) (Lam' Done (Var' VZ))))))


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
