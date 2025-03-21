"""
Reverse a linked list.

The reversed list is messy because there are many unreachable branches like
```
Project { e: Pair { left: Num(4), right: <a large tree> }, d: Right }
```

You can see in the picture of output AST (using `-ae` flag) that the list is indeed reversed.
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
