{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

-- De Bruijn and Co-De Bruijn syntax and conversions between them.

import Data.Proxy
import Data.Type.Equality

data Var env a where
  VZ :: Var (x : env) x
  VS :: Var env x -> Var (y : env) x

deriving instance Show (Var env a)

data DB env a where
  Var :: Var env a -> DB env a
  Lam :: DB (a : env) b -> DB env (a -> b)
  App :: DB env (a -> b) -> DB env a -> DB env b

deriving instance Show (DB env a)

dbId :: DB env (b -> b)
dbId = Lam (Var VZ)

dbConst :: DB env (b -> a -> b)
dbConst = Lam (Lam (Var (VS VZ)))

dbConst2 :: DB env (a -> b -> b)
dbConst2 = App dbConst dbId

dbFlip :: DB env ((a -> b -> c) -> b -> a -> c)
dbFlip = Lam (Lam (Lam (App (App (Var (VS (VS VZ))) (Var VZ)) (Var (VS VZ)))))

--

data Use a env env' where
  Use :: Use a env (a : env)
  Drop :: Use a env env

deriving instance Show (Use a env env')

data Split env env1 env2 where
  D :: Split '[] '[] '[]
  L :: Split env env1 env2 -> Split (x : env) (x : env1) env2
  R :: Split env env1 env2 -> Split (x : env) env1 (x : env2)
  B :: Split env env1 env2 -> Split (x : env) (x : env1) (x : env2)

deriving instance Show (Split env env1 env2)

data CoDB env a where
  CoVar :: CoDB '[a] a
  CoLam :: Use a env env' -> CoDB env' b -> CoDB env (a -> b)
  CoApp :: Split env env1 env2 -> CoDB env1 (a -> b) -> CoDB env2 a -> CoDB env b

deriving instance Show (CoDB env a)

codbId :: CoDB '[] (b -> b)
codbId = CoLam Use CoVar

codbConst :: CoDB '[] (b -> a -> b)
codbConst = CoLam Use (CoLam Drop CoVar)

codbConst2 :: CoDB '[] (a -> b -> b)
codbConst2 = CoApp D codbConst codbId

codbFlip :: CoDB '[] ((a -> b -> c) -> b -> a -> c)
codbFlip = CoLam Use (CoLam Use (CoLam Use (CoApp (L (R (L D))) (CoApp (R (L D)) CoVar CoVar) CoVar)))

--

data HList f xs where
  HCons :: f x -> HList f xs -> HList f (x : xs)
  HNil :: HList f '[]

type (++) :: [k] -> [k] -> [k]
type family xs ++ ys where
  '[] ++ ys = ys
  (x : xs) ++ ys = x : (xs ++ ys)

-- Make sure 'xs' is not a stuck type family
seqHList :: HList Proxy xs -> a -> a
seqHList HNil x = x
seqHList (HCons Proxy h) x = seqHList h x

assoc :: HList Proxy xs -> Proxy ys -> Proxy zs -> ((xs ++ ys) ++ zs :~: xs ++ (ys ++ zs))
assoc HNil Proxy Proxy = Refl
assoc (HCons Proxy h) p1 p2 = case assoc h p1 p2 of Refl -> Refl

hAppend :: HList f xs -> HList f ys -> HList f (xs ++ ys)
hAppend HNil ys = ys
hAppend (HCons x xs) ys = HCons x (hAppend xs ys)

--

weakenVar :: HList Proxy env -> Proxy (x : env') -> Var (env ++ env') a -> Var (env ++ (x : env')) a
weakenVar HNil Proxy x = VS x
weakenVar (HCons _ xs) p (VS x) = VS (weakenVar xs p x)
weakenVar HCons {} _ VZ = VZ

weaken :: HList Proxy env -> Proxy (x : env') -> DB (env ++ env') a -> DB (env ++ (x : env')) a
weaken h p (Var v) = Var (weakenVar h p v)
weaken h p (Lam x) = Lam (weaken (HCons Proxy h) p x)
weaken h p (App x y) = App (weaken h p x) (weaken h p y)

--

fromCo :: CoDB env a -> DB env a
fromCo CoVar = Var VZ
fromCo (CoLam Use bdy) = Lam (fromCo bdy)
fromCo (CoLam Drop bdy) = Lam (weaken HNil Proxy (fromCo bdy))
fromCo (CoApp z x y) = app HNil z (fromCo x) (fromCo y)

app ::
  forall env env' env1 env2 a b.
  HList Proxy env ->
  Split env' env1 env2 ->
  DB (env ++ env1) (a -> b) ->
  DB (env ++ env2) a ->
  DB (env ++ env') b
app _ D x y = App x y
app h (L @env'' @env1' @env2' @x z) x y =
  let assoc' :: Proxy zs -> ((env ++ '[x]) ++ zs :~: env ++ (x : zs))
      assoc' = assoc h (Proxy @'[x])
   in case (assoc' (Proxy @env''), assoc' (Proxy @env1'), assoc' (Proxy @env2')) of
        (Refl, Refl, Refl) ->
          let y' = weaken h (Proxy @(x : env2')) y
           in app (hAppend h (HCons (Proxy @x) HNil)) z x y'
app h (R @env'' @env1' @env2' @x z) x y =
  let assoc' :: Proxy zs -> ((env ++ '[x]) ++ zs :~: env ++ (x : zs))
      assoc' = assoc h (Proxy @'[x])
   in case (assoc' (Proxy @env''), assoc' (Proxy @env1'), assoc' (Proxy @env2')) of
        (Refl, Refl, Refl) ->
          let x' = weaken h (Proxy @(x : env1')) x
           in app (hAppend h (HCons (Proxy @x) HNil)) z x' y
app h (B @env'' @env1' @env2' @x z) x y =
  let assoc' :: Proxy zs -> ((env ++ '[x]) ++ zs :~: env ++ (x : zs))
      assoc' = assoc h (Proxy @'[x])
   in case (assoc' (Proxy @env''), assoc' (Proxy @env1'), assoc' (Proxy @env2')) of
        (Refl, Refl, Refl) -> app (hAppend h (HCons (Proxy @x) HNil)) z x y
