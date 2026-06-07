/-
Progress and Preservation for typed language with arithmetic, booleans,
functions (de Bruijn), products, sums, fixpoints, and let-bindings.
-/

set_option linter.unusedVariables false

/- ========================================================================== Syntax ========================================================================== -/

inductive Ty : Type where | num | bool | unit | fn : Ty → Ty → Ty | prod : Ty → Ty → Ty | sum : Ty → Ty → Ty
  deriving Inhabited, DecidableEq

inductive AddOp : Type where | add | sub deriving Inhabited, DecidableEq
inductive MulOp : Type where | mul | dvd deriving Inhabited, DecidableEq
inductive RelOp : Type where | lt | gt | eq deriving Inhabited, DecidableEq
inductive Dir : Type where | L | R deriving Inhabited, DecidableEq

inductive Expr : Type where
  | num   : Int → Expr | addOp : AddOp → Expr → Expr → Expr | mulOp : MulOp → Expr → Expr → Expr
  | tru   : Expr | fls : Expr | relOp : RelOp → Expr → Expr → Expr
  | and   : Expr → Expr → Expr | or : Expr → Expr → Expr | if_ : Expr → Expr → Expr → Expr
  | var   : Nat → Expr | lam : Ty → Expr → Expr | app : Expr → Expr → Expr
  | unit  : Expr | pair : Expr → Expr → Expr | proj : Dir → Expr → Expr
  | inj   : Dir → Expr → Expr | case_ : Expr → Expr → Expr → Expr
  | fix_  : Ty → Expr → Expr | let_ : Expr → Expr → Expr
  deriving Inhabited, DecidableEq

inductive Value : Expr → Prop where
  | num : Value (Expr.num n) | tru : Value Expr.tru | fls : Value Expr.fls
  | unit : Value Expr.unit | lam : Value (Expr.lam τ e)
  | pair : Value (Expr.pair e₁ e₂) | inj : Value (Expr.inj d e) | var : Value (Expr.var i)

/- ========================================================================== Substitution ========================================================================== -/

def subst (k : Nat) (s : Expr) : Expr → Expr
  | Expr.num n => Expr.num n
  | Expr.addOp o l r => Expr.addOp o (subst k s l) (subst k s r)
  | Expr.mulOp o l r => Expr.mulOp o (subst k s l) (subst k s r)
  | Expr.tru => Expr.tru | Expr.fls => Expr.fls | Expr.unit => Expr.unit
  | Expr.relOp o l r => Expr.relOp o (subst k s l) (subst k s r)
  | Expr.and l r => Expr.and (subst k s l) (subst k s r)
  | Expr.or l r => Expr.or (subst k s l) (subst k s r)
  | Expr.if_ c t e => Expr.if_ (subst k s c) (subst k s t) (subst k s e)
  | Expr.var i => if i == k then s else Expr.var i
  | Expr.lam τ e => Expr.lam τ (subst (k+1) s e)
  | Expr.app f a => Expr.app (subst k s f) (subst k s a)
  | Expr.pair l r => Expr.pair (subst k s l) (subst k s r)
  | Expr.proj d e => Expr.proj d (subst k s e)
  | Expr.inj d e => Expr.inj d (subst k s e)
  | Expr.case_ e el er => Expr.case_ (subst k s e) (subst (k+1) s el) (subst (k+1) s er)
  | Expr.fix_ τ e => Expr.fix_ τ (subst (k+1) s e)
  | Expr.let_ e₁ e₂ => Expr.let_ (subst k s e₁) (subst (k+1) s e₂)

/- ========================================================================== Typing ========================================================================== -/

inductive Typing : List Ty → Expr → Ty → Prop where
  | num (Γ : List Ty) (n : Int) : Typing Γ (Expr.num n) Ty.num
  | tru (Γ : List Ty) : Typing Γ Expr.tru Ty.bool
  | fls (Γ : List Ty) : Typing Γ Expr.fls Ty.bool
  | unit (Γ : List Ty) : Typing Γ Expr.unit Ty.unit
  | addOp (Γ : List Ty) (op : AddOp) (l r : Expr) :
      Typing Γ l Ty.num → Typing Γ r Ty.num → Typing Γ (Expr.addOp op l r) Ty.num
  | mulOp (Γ : List Ty) (op : MulOp) (l r : Expr) :
      Typing Γ l Ty.num → Typing Γ r Ty.num → Typing Γ (Expr.mulOp op l r) Ty.num
  | relOp (Γ : List Ty) (op : RelOp) (l r : Expr) :
      Typing Γ l Ty.num → Typing Γ r Ty.num → Typing Γ (Expr.relOp op l r) Ty.bool
  | and (Γ : List Ty) (l r : Expr) :
      Typing Γ l Ty.bool → Typing Γ r Ty.bool → Typing Γ (Expr.and l r) Ty.bool
  | or (Γ : List Ty) (l r : Expr) :
      Typing Γ l Ty.bool → Typing Γ r Ty.bool → Typing Γ (Expr.or l r) Ty.bool
  | if_ (Γ : List Ty) (cnd t e : Expr) (τ : Ty) :
      Typing Γ cnd Ty.bool → Typing Γ t τ → Typing Γ e τ → Typing Γ (Expr.if_ cnd t e) τ
  | var (Γ : List Ty) (i : Fin Γ.length) (τ : Ty) (h : Γ.get i = some τ) : Typing Γ (Expr.var i) τ
  | lam (Γ : List Ty) (τ₁ : Ty) (e : Expr) (τ₂ : Ty) :
      Typing ([τ₁] ++ Γ) e τ₂ → Typing Γ (Expr.lam τ₁ e) (Ty.fn τ₁ τ₂)
  | app (Γ : List Ty) (f a : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ f (Ty.fn τ₁ τ₂) → Typing Γ a τ₁ → Typing Γ (Expr.app f a) τ₂
  | pair (Γ : List Ty) (l r : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ l τ₁ → Typing Γ r τ₂ → Typing Γ (Expr.pair l r) (Ty.prod τ₁ τ₂)
  | projL (Γ : List Ty) (e : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ e (Ty.prod τ₁ τ₂) → Typing Γ (Expr.proj Dir.L e) τ₁
  | projR (Γ : List Ty) (e : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ e (Ty.prod τ₁ τ₂) → Typing Γ (Expr.proj Dir.R e) τ₂
  | injL (Γ : List Ty) (e : Expr) (τ τ' : Ty) :
      Typing Γ e τ → Typing Γ (Expr.inj Dir.L e) (Ty.sum τ τ')
  | injR (Γ : List Ty) (e : Expr) (τ τ' : Ty) :
      Typing Γ e τ → Typing Γ (Expr.inj Dir.R e) (Ty.sum τ' τ)
  | case_ (Γ : List Ty) (e el er : Expr) (τL τR τ : Ty) :
      Typing Γ e (Ty.sum τL τR) →
      Typing ([τL] ++ Γ) el τ → Typing ([τR] ++ Γ) er τ →
      Typing Γ (Expr.case_ e el er) τ
  | fix_ (Γ : List Ty) (τ : Ty) (e : Expr) :
      Typing ([τ] ++ Γ) e τ → Typing Γ (Expr.fix_ τ e) τ
  | let_ (Γ : List Ty) (e₁ e₂ : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ e₁ τ₁ → Typing ([τ₁] ++ Γ) e₂ τ₂ → Typing Γ (Expr.let_ e₁ e₂) τ₂

/- ========================================================================== Reduction ========================================================================== -/

inductive Step : Expr → Expr → Prop where
  | addL (op : AddOp) (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.addOp op e₁ e₂) (Expr.addOp op e₁' e₂)
  | addR (op : AddOp) (v₁ e₂ e₂' : Expr) (hv : Value v₁) (h : Step e₂ e₂') : Step (Expr.addOp op v₁ e₂) (Expr.addOp op v₁ e₂')
  | addAdd (n₁ n₂ : Int) : Step (Expr.addOp AddOp.add (Expr.num n₁) (Expr.num n₂)) (Expr.num (n₁ + n₂))
  | addSub (n₁ n₂ : Int) : Step (Expr.addOp AddOp.sub (Expr.num n₁) (Expr.num n₂)) (Expr.num (n₁ - n₂))
  | mulL (op : MulOp) (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.mulOp op e₁ e₂) (Expr.mulOp op e₁' e₂)
  | mulR (op : MulOp) (v₁ e₂ e₂' : Expr) (hv : Value v₁) (h : Step e₂ e₂') : Step (Expr.mulOp op v₁ e₂) (Expr.mulOp op v₁ e₂')
  | mulMul (n₁ n₂ : Int) : Step (Expr.mulOp MulOp.mul (Expr.num n₁) (Expr.num n₂)) (Expr.num (n₁ * n₂))
  | mulDiv (n₁ n₂ : Int) : Step (Expr.mulOp MulOp.dvd (Expr.num n₁) (Expr.num n₂)) (Expr.num (n₁ / n₂))
  | relL (op : RelOp) (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.relOp op e₁ e₂) (Expr.relOp op e₁' e₂)
  | relR (op : RelOp) (v₁ e₂ e₂' : Expr) (hv : Value v₁) (h : Step e₂ e₂') : Step (Expr.relOp op v₁ e₂) (Expr.relOp op v₁ e₂')
  | relLtT (n₁ n₂ : Int) (h : n₁ < n₂) : Step (Expr.relOp RelOp.lt (Expr.num n₁) (Expr.num n₂)) Expr.tru
  | relLtF (n₁ n₂ : Int) (h : ¬ n₁ < n₂) : Step (Expr.relOp RelOp.lt (Expr.num n₁) (Expr.num n₂)) Expr.fls
  | relGtT (n₁ n₂ : Int) (h : n₁ > n₂) : Step (Expr.relOp RelOp.gt (Expr.num n₁) (Expr.num n₂)) Expr.tru
  | relGtF (n₁ n₂ : Int) (h : ¬ n₁ > n₂) : Step (Expr.relOp RelOp.gt (Expr.num n₁) (Expr.num n₂)) Expr.fls
  | relEqT (n₁ n₂ : Int) (h : n₁ = n₂) : Step (Expr.relOp RelOp.eq (Expr.num n₁) (Expr.num n₂)) Expr.tru
  | relEqF (n₁ n₂ : Int) (h : n₁ ≠ n₂) : Step (Expr.relOp RelOp.eq (Expr.num n₁) (Expr.num n₂)) Expr.fls
  | andL (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.and e₁ e₂) (Expr.and e₁' e₂)
  | andTrue (e₂ : Expr) : Step (Expr.and Expr.tru e₂) e₂
  | andFalse (e₂ : Expr) : Step (Expr.and Expr.fls e₂) Expr.fls
  | orL (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.or e₁ e₂) (Expr.or e₁' e₂)
  | orTrue (e₂ : Expr) : Step (Expr.or Expr.tru e₂) Expr.tru
  | orFalse (e₂ : Expr) : Step (Expr.or Expr.fls e₂) e₂
  | ifL (c c' t e : Expr) (h : Step c c') : Step (Expr.if_ c t e) (Expr.if_ c' t e)
  | ifTrue (t e : Expr) : Step (Expr.if_ Expr.tru t e) t
  | ifFalse (t e : Expr) : Step (Expr.if_ Expr.fls t e) e
  | appL (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.app e₁ e₂) (Expr.app e₁' e₂)
  | appR (v₁ e₂ e₂' : Expr) (hv : Value v₁) (h : Step e₂ e₂') : Step (Expr.app v₁ e₂) (Expr.app v₁ e₂')
  | appLam (τ : Ty) (body v : Expr) (hv : Value v) : Step (Expr.app (Expr.lam τ body) v) (subst 0 v body)
  | pairL (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.pair e₁ e₂) (Expr.pair e₁' e₂)
  | pairR (v₁ e₂ e₂' : Expr) (hv : Value v₁) (h : Step e₂ e₂') : Step (Expr.pair v₁ e₂) (Expr.pair v₁ e₂')
  | proj_step (e e' : Expr) (d : Dir) (h : Step e e') : Step (Expr.proj d e) (Expr.proj d e')
  | projL_val (l r : Expr) : Step (Expr.proj Dir.L (Expr.pair l r)) l
  | projR_val (l r : Expr) : Step (Expr.proj Dir.R (Expr.pair l r)) r
  | inj_step (e e' : Expr) (d : Dir) (h : Step e e') : Step (Expr.inj d e) (Expr.inj d e')
  | case_step (e e' el er : Expr) (h : Step e e') : Step (Expr.case_ e el er) (Expr.case_ e' el er)
  | caseL_val (v el er : Expr) : Step (Expr.case_ (Expr.inj Dir.L v) el er) (subst 0 v el)
  | caseR_val (v el er : Expr) : Step (Expr.case_ (Expr.inj Dir.R v) el er) (subst 0 v er)
  | fix_step (τ : Ty) (body : Expr) : Step (Expr.fix_ τ body) (subst 0 (Expr.fix_ τ body) body)
  | let_step (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.let_ e₁ e₂) (Expr.let_ e₁' e₂)
  | let_val (v e₂ : Expr) (hv : Value v) : Step (Expr.let_ v e₂) (subst 0 v e₂)

/- ========================================================================== Canonical forms ========================================================================== -/

theorem canonical_num (e : Expr) (hv : Value e) (ht : Typing [] e Ty.num) : ∃ n : Int, e = Expr.num n := by
  cases hv
  case num => rename_i n; exact ⟨n, rfl⟩
  case var =>
    cases ht
    · rename_i i h
      exact absurd i.isLt (Nat.not_lt_zero _)
  all_goals { cases ht }

theorem canonical_bool (e : Expr) (hv : Value e) (ht : Typing [] e Ty.bool) : e = Expr.tru ∨ e = Expr.fls := by
  cases hv
  case tru => exact Or.inl rfl
  case fls => exact Or.inr rfl
  case var =>
    cases ht
    · rename_i i h
      exact absurd i.isLt (Nat.not_lt_zero _)
  all_goals { cases ht }

theorem canonical_fn (e : Expr) (hv : Value e) (ht : Typing [] e (Ty.fn τ₁ τ₂)) : ∃ (σ : Ty) (b : Expr), e = Expr.lam σ b := by
  cases hv
  case lam => rename_i σ b; exact ⟨σ, b, rfl⟩
  case var =>
    cases ht
    · rename_i i h
      exact absurd i.isLt (Nat.not_lt_zero _)
  all_goals { cases ht }

theorem canonical_prod (e : Expr) (hv : Value e) (ht : Typing [] e (Ty.prod τ₁ τ₂)) : ∃ l r : Expr, e = Expr.pair l r := by
  cases hv
  case pair => rename_i l r; exact ⟨l, r, rfl⟩
  case var =>
    cases ht
    · rename_i i h
      exact absurd i.isLt (Nat.not_lt_zero _)
  all_goals { cases ht }

theorem canonical_sum (e : Expr) (hv : Value e) (ht : Typing [] e (Ty.sum τ₁ τ₂)) : ∃ (d : Dir) (v : Expr), e = Expr.inj d v := by
  cases hv
  case inj => rename_i d v; exact ⟨d, v, rfl⟩
  case var =>
    cases ht
    · rename_i i h
      exact absurd i.isLt (Nat.not_lt_zero _)
  all_goals { cases ht }

/- ========================================================================== Progress ========================================================================== -/

theorem progress (e : Expr) (τ : Ty) (h : Typing [] e τ) : Value e ∨ ∃ e', Step e e' := by
  induction e generalizing τ with
  | num n => left; exact Value.num
  | tru => left; exact Value.tru
  | fls => left; exact Value.fls
  | unit => left; exact Value.unit
  | addOp op l r ih_l ih_r =>
    match h with
    | Typing.addOp _ _ _ _ hl hr =>
      rcases ih_l Ty.num hl with (hvl | ⟨l', hl'⟩)
      · rcases ih_r Ty.num hr with (hvr | ⟨r', hr'⟩)
        · rcases canonical_num l hvl hl with ⟨nl, rfl⟩; rcases canonical_num r hvr hr with ⟨nr, rfl⟩
          right; cases op with | add => exact ⟨_, Step.addAdd nl nr⟩ | sub => exact ⟨_, Step.addSub nl nr⟩
        · right; exact ⟨_, Step.addR op l r r' hvl hr'⟩
      · right; exact ⟨_, Step.addL op l l' r hl'⟩
  | mulOp op l r ih_l ih_r =>
    match h with
    | Typing.mulOp _ _ _ _ hl hr =>
      rcases ih_l Ty.num hl with (hvl | ⟨l', hl'⟩)
      · rcases ih_r Ty.num hr with (hvr | ⟨r', hr'⟩)
        · rcases canonical_num l hvl hl with ⟨nl, rfl⟩; rcases canonical_num r hvr hr with ⟨nr, rfl⟩
          right; cases op with
          | mul => exact ⟨_, Step.mulMul nl nr⟩
          | dvd => exact ⟨_, Step.mulDiv nl nr⟩
        · right; exact ⟨_, Step.mulR op l r r' hvl hr'⟩
      · right; exact ⟨_, Step.mulL op l l' r hl'⟩
  | relOp op l r ih_l ih_r =>
    match h with
    | Typing.relOp _ _ _ _ hl hr =>
      rcases ih_l Ty.num hl with (hvl | ⟨l', hl'⟩)
      · rcases ih_r Ty.num hr with (hvr | ⟨r', hr'⟩)
        · rcases canonical_num l hvl hl with ⟨nl, rfl⟩; rcases canonical_num r hvr hr with ⟨nr, rfl⟩
          right; cases op with
          | lt =>
            by_cases hlt : nl < nr
            · exact ⟨_, Step.relLtT nl nr hlt⟩
            · exact ⟨_, Step.relLtF nl nr hlt⟩
          | gt =>
            by_cases hgt : nl > nr
            · exact ⟨_, Step.relGtT nl nr hgt⟩
            · exact ⟨_, Step.relGtF nl nr hgt⟩
          | eq =>
            by_cases heq : nl = nr
            · exact ⟨_, Step.relEqT nl nr heq⟩
            · exact ⟨_, Step.relEqF nl nr heq⟩
        · right; exact ⟨_, Step.relR op l r r' hvl hr'⟩
      · right; exact ⟨_, Step.relL op l l' r hl'⟩
  | and l r ih_l ih_r =>
    match h with
    | Typing.and _ _ _ hl hr =>
      rcases ih_l Ty.bool hl with (hvl | ⟨l', hl'⟩)
      · rcases canonical_bool l hvl hl with (rfl | rfl)
        · right; exact ⟨r, Step.andTrue r⟩
        · right; exact ⟨_, Step.andFalse r⟩
      · right; exact ⟨_, Step.andL l l' r hl'⟩
  | or l r ih_l ih_r =>
    match h with
    | Typing.or _ _ _ hl hr =>
      rcases ih_l Ty.bool hl with (hvl | ⟨l', hl'⟩)
      · rcases canonical_bool l hvl hl with (rfl | rfl)
        · right; exact ⟨_, Step.orTrue r⟩
        · right; exact ⟨r, Step.orFalse r⟩
      · right; exact ⟨_, Step.orL l l' r hl'⟩
  | if_ c t e ih_c ih_t ih_e =>
    match h with
    | Typing.if_ _ _ _ _ τ' hc ht he =>
      rcases ih_c Ty.bool hc with (hvc | ⟨c', hc'⟩)
      · rcases canonical_bool c hvc hc with (rfl | rfl)
        · right; exact ⟨t, Step.ifTrue t e⟩
        · right; exact ⟨e, Step.ifFalse t e⟩
      · right; exact ⟨_, Step.ifL c c' t e hc'⟩
  | var i =>
    match h with
    | Typing.var _ i_fin _ _ => exact absurd i_fin.isLt (Nat.not_lt_zero i_fin.val)
  | lam σ body ih_body => left; exact Value.lam
  | app f a ih_f ih_a =>
    match h with
    | Typing.app _ _ _ τ₁ τ₂ hf ha =>
      rcases ih_f (Ty.fn τ₁ τ₂) hf with (hvf | ⟨f', hf'⟩)
      · match hf with
        | Typing.lam _ _ body _ hb =>
          rcases ih_a τ₁ ha with (hva | ⟨a', ha'⟩)
          · right; exact ⟨_, Step.appLam τ₁ body a hva⟩
          · right; exact ⟨_, Step.appR (Expr.lam τ₁ body) a a' Value.lam ha'⟩
      · right; exact ⟨_, Step.appL f f' a hf'⟩
  | pair l r ih_l ih_r =>
    match h with
    | Typing.pair _ _ _ τ₁ τ₂ hl hr =>
      rcases ih_l τ₁ hl with (hvl | ⟨l', hl'⟩)
      · rcases ih_r τ₂ hr with (hvr | ⟨r', hr'⟩)
        · left; exact Value.pair
        · right; exact ⟨_, Step.pairR l r r' hvl hr'⟩
      · right; exact ⟨_, Step.pairL l l' r hl'⟩
  | proj d e ih_e =>
    match h with
    | Typing.projL _ _ _ _ he =>
      rcases ih_e _ he with (hve | ⟨e', he'⟩)
      · rcases canonical_prod e hve he with ⟨l, r, rfl⟩; right; exact ⟨l, Step.projL_val l r⟩
      · right; exact ⟨_, Step.proj_step e e' Dir.L he'⟩
    | Typing.projR _ _ _ _ he =>
      rcases ih_e _ he with (hve | ⟨e', he'⟩)
      · rcases canonical_prod e hve he with ⟨l, r, rfl⟩; right; exact ⟨r, Step.projR_val l r⟩
      · right; exact ⟨_, Step.proj_step e e' Dir.R he'⟩
  | inj d e ih_e =>
    cases h
    case injL =>
      rcases ih_e _ (by assumption) with (hve | ⟨e', he'⟩)
      · left; exact Value.inj
      · right; exact ⟨_, Step.inj_step e e' Dir.L he'⟩
    case injR =>
      rcases ih_e _ (by assumption) with (hve | ⟨e', he'⟩)
      · left; exact Value.inj
      · right; exact ⟨_, Step.inj_step e e' Dir.R he'⟩
    all_goals { apply False.elim; exact ?_ }
  | case_ e el er ih_e ih_el ih_er =>
    match h with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her =>
      rcases ih_e (Ty.sum τL τR) hse with (hve | ⟨e', he'⟩)
      · rcases canonical_sum e hve hse with ⟨d, v, rfl⟩
        cases d with
        | L => right; exact ⟨_, Step.caseL_val v el er⟩
        | R => right; exact ⟨_, Step.caseR_val v el er⟩
      · right; exact ⟨_, Step.case_step e e' el er he'⟩
  | fix_ σ body ih_body =>
    match h with
    | Typing.fix_ _ _ _ he => right; exact ⟨_, Step.fix_step σ body⟩
  | let_ e₁ e₂ ih₁ ih₂ =>
    match h with
    | Typing.let_ _ _ _ τ₁ τ₂ h₁ h₂ =>
      rcases ih₁ τ₁ h₁ with (hv | ⟨e₁', he₁'⟩)
      · right; exact ⟨_, Step.let_val e₁ e₂ hv⟩
      · right; exact ⟨_, Step.let_step e₁ e₁' e₂ he₁'⟩

/- ========================================================================== Helper Theorems ========================================================================== -/

theorem get_append_singleton {Γ : List Ty} {σ : Ty} {j : Fin ((Γ ++ [σ]).length)} (h_eq : j.val = Γ.length) : (Γ ++ [σ]).get j = σ := by
  induction Γ with
  | nil => simp
  | cons τ Γ ih =>
    cases j; rename_i val isLt
    cases val with
    | zero => have : 0 = (τ :: Γ).length := h_eq; simp at this
    | succ n =>
      have h_lt : n < (Γ ++ [σ]).length := by
        have : n.succ < ((τ :: Γ) ++ [σ]).length := isLt; simpa using this
      have h_eq' : n = Γ.length := by simp at h_eq; exact h_eq
      simpa using ih (j := ⟨n, h_lt⟩) h_eq'

theorem get_append_left {Γ Δ : List Ty} {i : Fin Γ.length} {hi : i.val < (Γ ++ Δ).length} : (Γ ++ Δ).get ⟨i.val, hi⟩ = Γ.get i := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | cons τ Γ ih =>
    cases i; rename_i val isLt
    cases val with
    | zero => rfl
    | succ n =>
      have h_n_lt : n < Γ.length := by simp at isLt; exact isLt
      have hi_n : n < (Γ ++ Δ).length := by
        have : n.succ < ((τ :: Γ) ++ Δ).length := hi; simpa using this
      simpa using ih (i := ⟨n, h_n_lt⟩) (hi := hi_n)

theorem weakening {Γ' : List Ty} {e : Expr} {τ : Ty} (h : Typing Γ' e τ) (Δ : List Ty) : Typing (Γ' ++ Δ) e τ := by
  induction h generalizing Δ with
  | num Γ n => exact Typing.num (Γ ++ Δ) n
  | tru Γ => exact Typing.tru (Γ ++ Δ)
  | fls Γ => exact Typing.fls (Γ ++ Δ)
  | unit Γ => exact Typing.unit (Γ ++ Δ)
  | addOp Γ op l r hl hr ih_l ih_r => exact Typing.addOp (Γ ++ Δ) op l r (ih_l Δ) (ih_r Δ)
  | mulOp Γ op l r hl hr ih_l ih_r => exact Typing.mulOp (Γ ++ Δ) op l r (ih_l Δ) (ih_r Δ)
  | relOp Γ op l r hl hr ih_l ih_r => exact Typing.relOp (Γ ++ Δ) op l r (ih_l Δ) (ih_r Δ)
  | and Γ l r hl hr ih_l ih_r => exact Typing.and (Γ ++ Δ) l r (ih_l Δ) (ih_r Δ)
  | or Γ l r hl hr ih_l ih_r => exact Typing.or (Γ ++ Δ) l r (ih_l Δ) (ih_r Δ)
  | if_ Γ cnd t e σ hc ht he ih_c ih_t ih_e => exact Typing.if_ (Γ ++ Δ) cnd t e σ (ih_c Δ) (ih_t Δ) (ih_e Δ)
  | var Γ i τ hget =>
    have hi : i.val < (Γ ++ Δ).length := by
      have h_i_lt : i.val < Γ.length := i.isLt
      have h_len : Γ.length ≤ (Γ ++ Δ).length := by simp
      exact Nat.lt_of_lt_of_le h_i_lt h_len
    let i' : Fin (Γ ++ Δ).length := ⟨i.val, hi⟩
    have hget_val : (Γ ++ Δ).get i' = Γ.get i := get_append_left (i := i) (hi := hi)
    have hget' : (Γ ++ Δ).get i' = some τ := (congrArg (fun t : Ty => some t) hget_val).trans hget
    exact Typing.var (Γ ++ Δ) i' τ hget'
  | lam Γ τ₁ e τ₂ hb ih => exact Typing.lam (Γ ++ Δ) τ₁ e τ₂ (by simpa [List.append_assoc] using ih Δ)
  | app Γ f a τ₁ τ₂ hf ha ih_f ih_a => exact Typing.app (Γ ++ Δ) f a τ₁ τ₂ (ih_f Δ) (ih_a Δ)
  | pair Γ l r τ₁ τ₂ hl hr ih_l ih_r => exact Typing.pair (Γ ++ Δ) l r τ₁ τ₂ (ih_l Δ) (ih_r Δ)
  | projL Γ e τ₁ τ₂ he ih => exact Typing.projL (Γ ++ Δ) e τ₁ τ₂ (ih Δ)
  | projR Γ e τ₁ τ₂ he ih => exact Typing.projR (Γ ++ Δ) e τ₁ τ₂ (ih Δ)
  | injL Γ e τ τ' he ih => exact Typing.injL (Γ ++ Δ) e τ τ' (ih Δ)
  | injR Γ e τ τ' he ih => exact Typing.injR (Γ ++ Δ) e τ τ' (ih Δ)
  | case_ Γ e el er τL τR τ hse hel her ih_se ih_el ih_er =>
    have h_el : Typing ([τL] ++ (Γ ++ Δ)) el τ := by simpa [List.append_assoc] using ih_el Δ
    have h_er : Typing ([τR] ++ (Γ ++ Δ)) er τ := by simpa [List.append_assoc] using ih_er Δ
    exact Typing.case_ (Γ ++ Δ) e el er τL τR τ (ih_se Δ) h_el h_er
  | fix_ Γ τ e hb ih => exact Typing.fix_ (Γ ++ Δ) τ e (by simpa [List.append_assoc] using ih Δ)
  | let_ Γ e₁ e₂ τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
    have h₂' : Typing ([τ₁] ++ (Γ ++ Δ)) e₂ τ₂ := by simpa [List.append_assoc] using ih₂ Δ
    exact Typing.let_ (Γ ++ Δ) e₁ e₂ τ₁ τ₂ (ih₁ Δ) h₂'

theorem subst_typing (s e : Expr) (τ σ : Ty) (Γ : List Ty)
    (h_e : Typing (Γ ++ [σ]) e τ) (h_s : Typing [] s σ) : Typing Γ (subst (Γ.length) s e) τ := by
  induction e generalizing Γ τ with
  | num n => cases h_e; case num => simp [subst]; exact Typing.num Γ n
  | tru => cases h_e; case tru => simp [subst]; exact Typing.tru Γ
  | fls => cases h_e; case fls => simp [subst]; exact Typing.fls Γ
  | unit => cases h_e; case unit => simp [subst]; exact Typing.unit Γ
  | addOp op l r ih_l ih_r => cases h_e; case addOp =>
    simp [subst]; rename_i hl hr; apply Typing.addOp Γ op _ _ (ih_l Ty.num Γ hl) (ih_r Ty.num Γ hr)
  | mulOp op l r ih_l ih_r => cases h_e; case mulOp =>
    simp [subst]; rename_i hl hr; apply Typing.mulOp Γ op _ _ (ih_l Ty.num Γ hl) (ih_r Ty.num Γ hr)
  | relOp op l r ih_l ih_r => cases h_e; case relOp =>
    simp [subst]; rename_i hl hr; apply Typing.relOp Γ op _ _ (ih_l Ty.num Γ hl) (ih_r Ty.num Γ hr)
  | and l r ih_l ih_r => cases h_e; case and =>
    simp [subst]; rename_i hl hr; apply Typing.and Γ _ _ (ih_l Ty.bool Γ hl) (ih_r Ty.bool Γ hr)
  | or l r ih_l ih_r => cases h_e; case or =>
    simp [subst]; rename_i hl hr; apply Typing.or Γ _ _ (ih_l Ty.bool Γ hl) (ih_r Ty.bool Γ hr)
  | if_ cnd t e ih_c ih_t ih_e => cases h_e; case if_ =>
    simp [subst]; rename_i hc ht he; apply Typing.if_ Γ _ _ _ _ (ih_c Ty.bool Γ hc) (ih_t _ Γ ht) (ih_e _ Γ he)
  | var i => cases h_e; case var hi hget =>
    by_cases h_eq : hi.val = Γ.length
    · have h_σ_eq : σ = τ := by
        have h_val : (Γ ++ [σ]).get hi = σ := get_append_singleton (j := hi) h_eq
        have heq1 : some ((Γ ++ [σ]).get hi) = some σ := congrArg some h_val
        exact Option.some.inj (heq1.symm.trans hget)
      subst h_σ_eq; simp [subst, h_eq]; exact weakening h_s Γ
    · have h_lt : hi.val < Γ.length := by
        have h_bound : hi.val < (Γ ++ [σ]).length := hi.isLt
        have h_len : (Γ ++ [σ]).length = Γ.length + 1 := by simp
        have : hi.val < Γ.length + 1 := by simpa [h_len] using h_bound
        omega
      simp [subst, h_eq]
      have hget' : some (Γ.get ⟨hi.val, h_lt⟩) = some τ := by
        have h_val : (Γ ++ [σ]).get hi = Γ.get ⟨hi.val, h_lt⟩ :=
          get_append_left (i := ⟨hi.val, h_lt⟩) (hi := hi.isLt)
        have heq : some ((Γ ++ [σ]).get hi) = some (Γ.get ⟨hi.val, h_lt⟩) := congrArg some h_val
        exact heq.symm ▸ hget
      exact Typing.var Γ ⟨hi.val, h_lt⟩ τ hget'
  | lam τ₁ body ih => cases h_e; case lam =>
    simp [subst]; rename_i τ₂ hb; apply Typing.lam Γ τ₁ _ τ₂ (ih τ₂ (τ₁ :: Γ) hb)
  | app f a ih_f ih_a => cases h_e; case app =>
    simp [subst]; rename_i τ₁ ha hf
    apply Typing.app Γ _ _ τ₁ _ (ih_f (Ty.fn τ₁ _) Γ hf) (ih_a τ₁ Γ ha)
  | pair l r ih_l ih_r => cases h_e; case pair =>
    simp [subst]; rename_i τ₁ τ₂ hl hr; apply Typing.pair Γ _ _ τ₁ τ₂ (ih_l τ₁ Γ hl) (ih_r τ₂ Γ hr)
  | proj d e ih =>
    cases h_e
    case projL =>
      simp [subst]; rename_i τ₂ he; apply Typing.projL Γ _ _ τ₂ (ih (Ty.prod τ τ₂) Γ he)
    case projR =>
      simp [subst]; rename_i τ₁ he; apply Typing.projR Γ _ τ₁ _ (ih (Ty.prod τ₁ τ) Γ he)
  | inj d e ih =>
    cases h_e
    case injL =>
      simp [subst]; rename_i τ₁ τ₂ he; apply Typing.injL Γ _ τ₁ τ₂ (ih τ₁ Γ he)
    case injR =>
      simp [subst]; rename_i τ₁ τ₂ he; apply Typing.injR Γ _ τ₁ τ₂ (ih τ₁ Γ he)
  | case_ scrut el er ih_scrut ih_el ih_er =>
    match h_e with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her =>
      simp [subst]
      apply Typing.case_ Γ _ _ _ τL τR τ'
        (ih_scrut (Ty.sum τL τR) Γ hse)
        (ih_el τ' (τL :: Γ) (by simpa [List.append_assoc] using hel))
        (ih_er τ' (τR :: Γ) (by simpa [List.append_assoc] using her))
  | fix_ τ₁ body ih =>
    match h_e with
    | Typing.fix_ _ _ _ hb =>
      simp [subst]; apply Typing.fix_ Γ τ₁ _ (ih τ₁ (τ₁ :: Γ) (by
        simpa [List.append_assoc] using hb))
  | let_ e₁ e₂ ih₁ ih₂ =>
    match h_e with
    | Typing.let_ _ _ _ τ₁ τ₂ h₁ h₂ =>
      simp [subst]; apply Typing.let_ Γ _ _ τ₁ τ₂ (ih₁ τ₁ Γ h₁) (ih₂ τ₂ (τ₁ :: Γ) (by
        simpa [List.append_assoc] using h₂))

/- ========================================================================== Preservation ========================================================================== -/

theorem preservation (e e' : Expr) (τ : Ty) (h : Typing [] e τ) (hstep : Step e e') : Typing [] e' τ := by
  induction hstep generalizing τ with
  | addL op e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.addOp _ _ _ _ hl hr => exact Typing.addOp [] op _ _ (ih Ty.num hl) hr
  | addR op v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.addOp _ _ _ _ hl hr => exact Typing.addOp [] op _ _ hl (ih Ty.num hr)
  | addAdd n₁ n₂ =>
    match h with
    | Typing.addOp _ _ _ _ _ _ => exact Typing.num [] (n₁ + n₂)
  | addSub n₁ n₂ =>
    match h with
    | Typing.addOp _ _ _ _ _ _ => exact Typing.num [] (n₁ - n₂)
  | mulL op e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.mulOp _ _ _ _ hl hr => exact Typing.mulOp [] op _ _ (ih Ty.num hl) hr
  | mulR op v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.mulOp _ _ _ _ hl hr => exact Typing.mulOp [] op _ _ hl (ih Ty.num hr)
  | mulMul n₁ n₂ =>
    match h with
    | Typing.mulOp _ _ _ _ _ _ => exact Typing.num [] (n₁ * n₂)
  | mulDiv n₁ n₂ =>
    match h with
    | Typing.mulOp _ _ _ _ _ _ => exact Typing.num [] (n₁ / n₂)
  | relL op e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.relOp _ _ _ _ hl hr => exact Typing.relOp [] op _ _ (ih Ty.num hl) hr
  | relR op v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.relOp _ _ _ _ hl hr => exact Typing.relOp [] op _ _ hl (ih Ty.num hr)
  | relLtT n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.tru []
  | relLtF n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.fls []
  | relGtT n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.tru []
  | relGtF n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.fls []
  | relEqT n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.tru []
  | relEqF n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.fls []
  | andL e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.and _ _ _ hl hr => exact Typing.and [] _ _ (ih Ty.bool hl) hr
  | andTrue e₂ =>
    match h with
    | Typing.and _ _ _ _ hr => exact hr
  | andFalse e₂ =>
    match h with
    | Typing.and _ _ _ _ _ => exact Typing.fls []
  | orL e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.or _ _ _ hl hr => exact Typing.or [] _ _ (ih Ty.bool hl) hr
  | orTrue e₂ =>
    match h with
    | Typing.or _ _ _ _ _ => exact Typing.tru []
  | orFalse e₂ =>
    match h with
    | Typing.or _ _ _ _ hr => exact hr
  | ifL c c' t e hstep' ih =>
    match h with
    | Typing.if_ _ _ _ _ τ' hc ht he => exact Typing.if_ [] _ _ _ τ' (ih Ty.bool hc) ht he
  | ifTrue t e =>
    match h with
    | Typing.if_ _ _ _ _ _ _ ht _ => exact ht
  | ifFalse t e =>
    match h with
    | Typing.if_ _ _ _ _ _ _ _ he => exact he
  | appL e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.app _ _ _ τ₁ τ₂ hf ha => exact Typing.app [] _ _ τ₁ τ₂ (ih (Ty.fn τ₁ τ₂) hf) ha
  | appR v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.app _ _ _ τ₁ τ₂ hf ha => exact Typing.app [] _ _ τ₁ τ₂ hf (ih τ₁ ha)
  | appLam τ₁ body v hv =>
    match h with
    | Typing.app _ _ _ _ τ₂ hf ha =>
      match hf with
      | Typing.lam _ _ _ _ hb => exact subst_typing v body τ₂ τ₁ (@List.nil Ty) hb ha
  | pairL e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.pair _ _ _ τ₁ τ₂ hl hr => exact Typing.pair [] _ _ τ₁ τ₂ (ih τ₁ hl) hr
  | pairR v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.pair _ _ _ τ₁ τ₂ hl hr => exact Typing.pair [] _ _ τ₁ τ₂ hl (ih τ₂ hr)
  | proj_step e e' d hstep' ih =>
    match h with
    | Typing.projL _ _ τ₁ τ₂ he => exact Typing.projL [] _ τ₁ τ₂ (ih (Ty.prod τ₁ τ₂) he)
    | Typing.projR _ _ τ₁ τ₂ he => exact Typing.projR [] _ τ₁ τ₂ (ih (Ty.prod τ₁ τ₂) he)
  | projL_val l r =>
    match h with
    | Typing.projL _ _ τ₁ τ₂ he =>
      match he with
      | Typing.pair _ _ _ _ _ hl _ => exact hl
  | projR_val l r =>
    match h with
    | Typing.projR _ _ τ₁ τ₂ he =>
      match he with
      | Typing.pair _ _ _ _ _ _ hr => exact hr
  | inj_step e e' d hstep' ih =>
    match h with
    | Typing.injL _ _ τ τ' he => exact Typing.injL [] _ τ τ' (ih τ he)
    | Typing.injR _ _ τ τ' he => exact Typing.injR [] _ τ τ' (ih τ he)
  | case_step e e' el er hstep' ih =>
    match h with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her => exact Typing.case_ [] _ _ _ τL τR τ' (ih (Ty.sum τL τR) hse) hel her
  | caseL_val v el er =>
    match h with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her =>
      match hse with
      | Typing.injL _ _ _ _ hv_ty => exact subst_typing v el τ' τL (@List.nil Ty) hel hv_ty
  | caseR_val v el er =>
    match h with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her =>
      match hse with
      | Typing.injR _ _ _ _ hv_ty => exact subst_typing v er τ' τR (@List.nil Ty) her hv_ty
  | fix_step τ₁ body =>
    match h with
    | Typing.fix_ _ _ _ hb =>
      have h_fix : Typing [] (Expr.fix_ τ₁ body) τ₁ := Typing.fix_ [] τ₁ body hb
      exact subst_typing (Expr.fix_ τ₁ body) body τ₁ τ₁ (@List.nil Ty) hb h_fix
  | let_step e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.let_ _ _ _ τ₁ τ₂ h₁ h₂ => exact Typing.let_ [] _ _ τ₁ τ₂ (ih τ₁ h₁) h₂
  | let_val v e₂ hv =>
    match h with
    | Typing.let_ _ _ _ τ₁ τ₂ h₁ h₂ => exact subst_typing v e₂ τ₂ τ₁ (@List.nil Ty) h₂ h₁
