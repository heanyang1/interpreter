"""
Reverse a linked list.
"""

from linkedlst import *

print(
    f"""
let reverse : forall a . {lst_ty("a")} -> {lst_ty("a")} =
    tyfun a -> fun (l : {lst_ty("a")}) ->
        (letrec aux : forall a . {lst_ty("a")} -> {lst_ty("a")} -> {lst_ty("a")} =
            tyfun a -> fun (l : {lst_ty("a")}) -> fun (acc : {lst_ty("a")}) ->
            case (unfold l) {{
                L(x) -> acc
                | R(t) -> (aux [a] (t.R) (fold (inj (t.L, acc) = R as unit + (a * {lst_ty("a")})) as {lst_ty("a")})) 
            }}
        in
            aux [a] l {lst([], "a")})
in
    reverse [num] {lst([1, 2, 3, 4], "num")}
    """
)
