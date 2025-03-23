"""
Some "macros" for linked lists.

Print a program that output the head of the list when running this program directly.
"""

def none(ty):
    return f"(tyfun {ty}_ -> inj () = L as unit + {ty}_)"


def some(ty):
    return f"(tyfun {ty}_ -> fun (x : {ty}_) -> inj x = R as unit + {ty}_)"


def lst_ty(ty):
    return f"(rec {ty}_ . unit + ({ty} * {ty}_))"


def lst(l, ty):
    if l == []:
        return f"(fold (inj () = L as unit + ({ty} * {lst_ty(ty)})) as {lst_ty(ty)})"
    else:
        return f"(fold (inj ({l[0]}, {lst(l[1:], ty)}) = R as unit + ({ty} * {lst_ty(ty)})) as {lst_ty(ty)})"


def head():
    return f"""
        (tyfun a ->
        fun (l : {lst_ty("a")}) ->
            case (unfold l) {{
                L(x) -> ({none("a")} [a])
                | R(t) -> ({some("a")} [a] (t.L))
            }})"""


def tail():
    return f"""
        (tyfun a ->
        fun (l : {lst_ty("a")}) ->
            case (unfold l) {{
                L(x) -> ({none("a")} [a])
                | R(t) -> ({some("a")} [a] (t.R))
            }})"""


if __name__ == "__main__":
    print(
        f"""
        case ({head()} [num] {lst([1, 2, 3, 4], "num")}) {{
            L(x) -> 0
            | R(t) -> t
        }}
        """
    )
