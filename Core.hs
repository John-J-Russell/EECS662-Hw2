module Core where

import Data.Map (Map)
import qualified Data.Map as Map

--------------------------------------------------------------------------------
-- Core syntax
--------------------------------------------------------------------------------

type Ident = String
data Core = CInt Integer | CAdd Core Core | CMult Core Core
          | CBool Bool | CIs0 Core | CIf Core Core Core
          | CVar Ident | CLam Ident CType Core | CApp Core Core | CLet Ident Core Core
          | CPair Core Core | CLetPair Ident Ident Core Core
          | CUnit | CLetUnit Core Core
          | CInl CType CType Core | CInr CType CType Core
          | CCase Core (Ident, Core) (Ident, Core)
          | CFix Core
          | CRef Core | CGet Core | CPut Core Core
  deriving (Eq, Show)

data CType = CTInt | CTBool | CTFun CType CType
           | CTProd CType CType | CTOne
           | CTSum CType CType
           | CTRef CType
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Typing and type checking
--------------------------------------------------------------------------------

type TEnv = [(Ident, CType)]

check :: TEnv -> Core -> Maybe CType
check _ (CInt _) =
    return CTInt
check g (CAdd e1 e2) =
    do CTInt <- check g e1
       CTInt <- check g e2
       return CTInt
check g (CMult e1 e2) =
    do CTInt <- check g e1
       CTInt <- check g e2
       return CTInt
check _ (CBool _) =
    return CTBool
check g (CIs0 e) =
    do CTInt <- check g e
       return CTBool
check g (CIf e1 e2 e3) =
    do CTBool <- check g e1
       t2 <- check g e2
       t3 <- check g e3
       if t2 == t3 then return t2 else Nothing
check g (CVar x) =
    lookup x g
check g (CLam x t1 e) =
    do t2 <- check ((x, t1):g) e
       return (CTFun t1 t2)
check g (CApp e1 e2) =
    do CTFun t1 t2 <- check g e1
       t1' <- check g e2
       if t1 == t1' then return t2 else Nothing
check g (CLet x e1 e2) =
    do t <- check g e1
       check ((x, t) : g) e2
check g (CPair e1 e2) =
    do t1 <- check g e1
       t2 <- check g e2
       return (CTProd t1 t2)
check g (CLetPair x1 x2 e1 e2) =
    do CTProd t1 t2 <- check g e1
       check ((x1, t1) : (x2, t2) : g) e2
check g CUnit =
    return CTOne
check g (CLetUnit e1 e2) =
    do CTOne <- check g e1
       check g e2
check g (CInl t1 t2 e) =
    do t <- check g e
       if t == t1 then return (CTSum t1 t2) else Nothing
check g (CInr t1 t2 e) =
    do t <- check g e
       if t == t2 then return (CTSum t1 t2) else Nothing
check g (CCase e (x1, e1) (x2, e2)) =
    do CTSum t1 t2 <- check g e
       u1 <- check ((x1, t1) : g) e1
       u2 <- check ((x2, t2) : g) e2
       if u1 == u2 then return u1 else Nothing
check g (CFix f) =
    do CTFun t (CTFun u v) <- check g f
       if t == CTFun u v then return t else Nothing
check g (CRef e) =
    CTRef (check g e) --See evaluation rules in specification
check g (CGet e) = --If e is a CTRef type "t", return "t"
    do CTRef x1 <- (check g e)
       return x1
check g (CPut key to_be_stored) = --key is the Ref, to_be_stored is the expr
    do CTRef cell_type = check g key --Get the type of the reference
       storage_type = check g to_be_stored --get type of expression
       if cell_type == storage_type then return CTOne else Nothing --return unit or nothing

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

data Value = VInt Integer | VBool Bool | VFun VEnv Ident Core
           | VPair Value Value | VUnit
           | VInl Value | VInr Value
           | VRef Integer
  deriving (Eq, Show)

run r = r

type VEnv = [(Ident, Value)]

eval :: VEnv -> Core -> Value
eval _ (CInt x) =
    VInt x
eval h (CAdd e1 e2) =
    let VInt x1 = eval h e1
        VInt x2 = eval h e2 in
    VInt (x1 + x2)
eval h (CMult e1 e2) =
    let VInt x1 = eval h e1
        VInt x2 = eval h e2 in
    VInt (x1 * x2)
eval _ (CBool b) =
    VBool b
eval h (CIs0 e) =
    let VInt x = eval h e in
    VBool (x == 0)
eval h (CIf e1 e2 e3) =
    let VBool b = eval h e1 in
    if b then eval h e2 else eval h e3
eval h (CVar x) =
    let Just v = lookup x h in v
eval h (CLam x _ e) =
    VFun h x e
eval h (CApp e1 e2) =
    let VFun h' x e = eval h e1
        v = eval h e2 in
    eval ((x, v) : h') e
eval h (CLet x e1 e2) =
    let v1 = eval h e1 in
    eval ((x,v1) : h) e2
eval h (CPair e1 e2) =
    let v1 = eval h e1
        v2 = eval h e2 in
    VPair v1 v2
eval h (CLetPair x1 x2 e1 e2) =
    let VPair v1 v2 = eval h e1 in
    eval ((x1, v1) : (x2, v2) : h) e2
eval h CUnit =
    VUnit
eval h (CLetUnit e1 e2) =
    let VUnit = eval h e1 in
    eval h e2
eval h (CInl _ _ e) =
    let v = eval h e in
    VInl v
eval h (CInr _ _ e) =
    let v = eval h e in
    VInr v
eval h (CCase e (x1, e1) (x2, e2)) =
    let v = eval h e in
    case v of
      VInl w -> eval ((x1, w) : h) e1
      VInr w -> eval ((x2, w) : h) e2
eval h (CFix f) =
    VFun h "$x" (CApp (CApp f (CFix f)) (CVar "$x"))
