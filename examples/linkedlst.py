"""
Some "macros" for linked lists.

Print a program that output the head of the list when running this program directly.
"""

def none():
    return "(tyfun a -> inj () = L as unit + a)"


def some():
    return "(tyfun a -> fun (x : a) -> inj x = R as unit + a)"


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
                L(x) -> ({none()} [a])
                | R(t) -> ({some()} [a] (t.L))
            }})"""


def tail():
    return f"""
        (tyfun a ->
        fun (l : {lst_ty("a")}) ->
            case (unfold l) {{
                L(x) -> ({none()} [a])
                | R(t) -> ({some()} [a] (t.R))
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
