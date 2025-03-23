from linkedlst import *
from tuple import *

def num_queue(ty):
    interfaces = tup_ty(
        [
            f"(unit -> {ty}_)",  # make
            f"({ty}_ -> num -> {ty}_)",  # enqueue
            f"({ty}_ -> unit + (num * {ty}_))",  # dequeue
        ]
    )
    return f"exists {ty}_. {interfaces}"


def list_num_queue():
    impl = tup_create(
        [
            f"fun (x: unit) -> {lst([], "num")}",  # make
            f"""
            fun (l : {lst_ty("num")}) -> fun (x : num) ->
                fold (inj (x, l) = R as unit + (num * {lst_ty("num")})) as {lst_ty("num")}
            """,  # enqueue
            f"""
            fix (f : {lst_ty("num")} -> unit + (num * {lst_ty("num")})) ->
                (fun (l: {lst_ty("num")}) -> case (unfold l) {{
                    L(x) -> inj () = L as unit + (num * {lst_ty("num")})
                    | R(q) -> case (unfold (q.R)) {{
                        L(x) -> inj (q.L, {lst([], "num")}) = R as unit + (num * {lst_ty("num")})
                        | R(q_p) -> case (f (q.R)) {{
                            L(x) -> inj () = L as unit + (num * {lst_ty("num")})
                            | R(t) -> (
                                (inj (
                                    t.L,
                                    fold (inj (q.L, t.R) = R as unit + (num * {lst_ty("num")})) as {lst_ty("num")}
                                ) = R as unit + (num * {lst_ty("num")}))
                            )
                        }}
                    }}
                }})
            """,  # dequeue
        ]
    )
    return f"""
export (
    {impl}
) without {lst_ty("num")} as {num_queue("a")}"""


if __name__ == "__main__":
    print(
        f"""
let qm_list: {num_queue("a")} = {list_num_queue()} in
import (qm, b) = qm_list in
(
    let q: b = {tup_get("qm", 0, 3)} () in
    let q: b = {tup_get("qm", 1, 3)} q 1 in
    let q: b = {tup_get("qm", 1, 3)} q 2 in
    let q: b = {tup_get("qm", 1, 3)} q 3 in
    let q: b = {tup_get("qm", 1, 3)} q 4 in
    {tup_get("qm", 2, 3)} q
)
"""
    )
