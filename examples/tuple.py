"""
Some "macros" for tuples.

Tuples are nested products.
"""


def tup_ty(ty):
    assert len(ty) >= 2
    if len(ty) == 2:
        return f"({ty[0]} * {ty[1]})"
    else:
        return f"({ty[0]} * {tup_ty(ty[1:])})"


def tup_create(exprs):
    assert len(exprs) >= 2
    if len(exprs) == 2:
        return f"({exprs[0]}, {exprs[1]})"
    else:
        return f"({exprs[0]}, {tup_create(exprs[1:])})"


def tup_get(expr, i, sz):
    def aux(cur, cnt, is_last):
        if cnt == 0:
            return f"{cur}.L"
        if cnt == 1:
            return f"{cur}.R" if is_last else aux(f"({cur}.R)", 0, False)
        else:
            return aux(f"({cur}.R)", cnt - 1, is_last)

    return aux(expr, i, i == sz - 1)

if __name__ == "__main__":
    types = ["num", "bool", "unit", "num", "bool"]
    idx = 0
    print(
        f"""
let f: {tup_ty(types)} -> {types[idx]} = fun (x: {tup_ty(["num", "bool", "unit", "num", "bool"])}) -> {tup_get("x", idx, len(types))}
in f ({tup_create(["1", "true", "()", "2", "false"])})
        """
    )
