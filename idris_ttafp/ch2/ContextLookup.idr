module ch2.ContextLookup

import Shared.ElemAtIdx
import ch2.Context
import ch2.AST

%default total

export
contextLookupBoundDecl : (c : Context) -> (n : Nat) -> Dec (sigma : Type' ** ElemAtIdx sigma (boundDecls c) n)
contextLookupBoundDecl (MkContext fds []) n = No (\(sigma ** elemPrf) => absurd elemPrf)
contextLookupBoundDecl (MkContext fds (t :: ts)) Z = Yes (t ** HereZ)
contextLookupBoundDecl (MkContext fds (t :: ts)) (S k) =
    case contextLookupBoundDecl (MkContext fds ts) k of
        (Yes (sigma ** prf)) => Yes (sigma ** ThereS prf)
        (No contra) => No (\(sigma ** elemPrf) => contra $ (sigma ** unThereS elemPrf))


contextLookupFreeDecl_impl : (c : Context) -> (len : Nat) -> len = length (freeDecls c) -> (v : FreeTermVariable) -> Dec (sigma : Type' ** ValueAtKey sigma (freeDecls c) v)
contextLookupFreeDecl_impl (MkContext (ps ** unique) bds) len len_prf v =
    case ps of
    [] => No (\(sigma ** elemPrf) => absurd elemPrf)
    ((w, sigma) :: xs) =>
        case decEq v w of
        Yes Refl => Yes (sigma ** ThisKey)
        (No not_head) =>
            case len of
            Z => absurd len_prf
            (S k) =>
                case contextLookupFreeDecl_impl (MkContext (xs ** uniqueUnCons unique) bds) k (succInjective _ _ len_prf) v of
                (Yes (tau ** prf)) => Yes (tau ** OtherKey unique prf)
                (No not_tail) => No (\(tau ** elemPrf) => not_tail (tau ** unOtherKey elemPrf not_head))

export
contextLookupFreeDecl : (c : Context) -> (v : FreeTermVariable) -> Dec (sigma : Type' ** ValueAtKey sigma (freeDecls c) v)
contextLookupFreeDecl c v = contextLookupFreeDecl_impl c (length (freeDecls c)) Refl v
