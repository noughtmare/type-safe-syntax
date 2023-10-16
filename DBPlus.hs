{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}

-- De Bruijn-like syntax extended with flexible environment filtering.

data Sel env env' where
  Keep :: Sel env env' -> Sel (x : env) (x : env')
  Drop :: Sel env env' -> Sel (x : env) env'
  KeepAll :: Sel env env
  DropAll :: Sel env '[]

deriving instance Show (Sel env env')

data DB env a where
  Sel :: Sel env env' -> DB env' a -> DB env a
  Var :: DB (x : env) x
  Lam :: DB (a : env) b -> DB env (a -> b)
  App :: DB env (a -> b) -> DB env a -> DB env b

deriving instance Show (DB env a)

dbId :: DB env (b -> b)
dbId = Lam Var

dbConst :: DB env (b -> a -> b)
dbConst = Lam (Lam (Sel (Drop KeepAll) Var))

dbConst2 :: DB env (a -> b -> b)
dbConst2 = App dbConst dbId

infixl 9 `App`

dbFlip :: DB env ((a -> b -> c) -> b -> a -> c)
dbFlip =
  Sel DropAll $
    Lam
      ( Sel (Keep DropAll) $
          Lam
            ( Sel (Keep (Keep DropAll)) $
                Lam
                  ( ( (Sel (Drop (Drop KeepAll)) Var)
                        `App` Var
                    )
                      `App` (Sel (Drop KeepAll) Var)
                  )
            )
      )
