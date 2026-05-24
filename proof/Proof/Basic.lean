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

/- ========================================================================== de Bruijn ops ========================================================================== -/

def shift (d cutoff : Nat) : Expr → Expr
  | Expr.num n => Expr.num n
  | Expr.addOp o l r => Expr.addOp o (shift d cutoff l) (shift d cutoff r)
  | Expr.mulOp o l r => Expr.mulOp o (shift d cutoff l) (shift d cutoff r)
  | Expr.tru => Expr.tru | Expr.fls => Expr.fls | Expr.unit => Expr.unit
  | Expr.relOp o l r => Expr.relOp o (shift d cutoff l) (shift d cutoff r)
  | Expr.and l r => Expr.and (shift d cutoff l) (shift d cutoff r)
  | Expr.or l r => Expr.or (shift d cutoff l) (shift d cutoff r)
  | Expr.if_ c t e => Expr.if_ (shift d cutoff c) (shift d cutoff t) (shift d cutoff e)
  | Expr.var i => if i ≥ cutoff then Expr.var (i + d) else Expr.var i
  | Expr.lam τ e => Expr.lam τ (shift d (cutoff+1) e)
  | Expr.app f a => Expr.app (shift d cutoff f) (shift d cutoff a)
  | Expr.pair l r => Expr.pair (shift d cutoff l) (shift d cutoff r)
  | Expr.proj dir e => Expr.proj dir (shift d cutoff e)
  | Expr.inj dir e => Expr.inj dir (shift d cutoff e)
  | Expr.case_ e el er => Expr.case_ (shift d cutoff e) (shift d (cutoff+1) el) (shift d (cutoff+1) er)
  | Expr.fix_ τ e => Expr.fix_ τ (shift d (cutoff+1) e)
  | Expr.let_ e₁ e₂ => Expr.let_ (shift d cutoff e₁) (shift d (cutoff+1) e₂)

def subst (k : Nat) (s : Expr) : Expr → Expr
  | Expr.num n => Expr.num n
  | Expr.addOp o l r => Expr.addOp o (subst k s l) (subst k s r)
  | Expr.mulOp o l r => Expr.mulOp o (subst k s l) (subst k s r)
  | Expr.tru => Expr.tru | Expr.fls => Expr.fls | Expr.unit => Expr.unit
  | Expr.relOp o l r => Expr.relOp o (subst k s l) (subst k s r)
  | Expr.and l r => Expr.and (subst k s l) (subst k s r)
  | Expr.or l r => Expr.or (subst k s l) (subst k s r)
  | Expr.if_ c t e => Expr.if_ (subst k s c) (subst k s t) (subst k s e)
  | Expr.var i => if i < k then Expr.var i else if i == k then shift k 0 s else Expr.var (i - 1)
  | Expr.lam τ e => Expr.lam τ (subst (k+1) s e)
  | Expr.app f a => Expr.app (subst k s f) (subst k s a)
  | Expr.pair l r => Expr.pair (subst k s l) (subst k s r)
  | Expr.proj d e => Expr.proj d (subst k s e)
  | Expr.inj d e => Expr.inj d (subst k s e)
  | Expr.case_ e el er => Expr.case_ (subst k s e) (subst (k+1) s el) (subst (k+1) s er)
  | Expr.fix_ τ e => Expr.fix_ τ (subst (k+1) s e)
  | Expr.let_ e₁ e₂ => Expr.let_ (subst k s e₁) (subst (k+1) s e₂)

/- ========================================================================== Context ========================================================================== -/

abbrev Ctx := Nat → Option Ty

def emptyCtx : Ctx := fun _ => none

def extendCtx (τ : Ty) (Γ : Ctx) : Ctx :=
  fun i =>
    match i with
    | 0 => some τ
    | i+1 => Γ i

def prepCtx (Δ : List Ty) (Γ : Ctx) (i : Nat) : Option Ty :=
  if h : i < Δ.length then some (Δ.get ⟨i, h⟩) else Γ (i - Δ.length)

theorem prepCtx_nil (Γ : Ctx) : prepCtx [] Γ = Γ := by
  ext i; simp [prepCtx]

theorem prepCtx_cons (τ : Ty) (Δ : List Ty) (Γ : Ctx) : prepCtx (τ :: Δ) Γ = extendCtx τ (prepCtx Δ Γ) := by
  ext i; cases i <;> simp [prepCtx, extendCtx]

theorem prepCtx_one (τ : Ty) (Γ : Ctx) : prepCtx [τ] Γ = extendCtx τ Γ := by
  calc
    prepCtx [τ] Γ = prepCtx (τ :: []) Γ := rfl
    _ = extendCtx τ (prepCtx [] Γ) := by rw [prepCtx_cons]
    _ = extendCtx τ Γ := by rw [prepCtx_nil]

theorem prepCtx_lookup_lt (Δ : List Ty) (Γ : Ctx) (i : Nat) (h : i < Δ.length) :
    prepCtx Δ Γ i = some (Δ.get ⟨i, h⟩) := by
  unfold prepCtx; simp [h]

theorem prepCtx_lookup_ge (Δ : List Ty) (Γ : Ctx) (i : Nat) (h : i ≥ Δ.length) :
    prepCtx Δ Γ i = Γ (i - Δ.length) := by
  unfold prepCtx
  have hnot : ¬ (i < Δ.length) := Nat.not_lt_of_ge h
  simp [hnot]

theorem extendCtx_prepCtx_comm (τ : Ty) (Δ : List Ty) (Γ : Ctx) :
    extendCtx τ (prepCtx Δ Γ) = prepCtx (τ :: Δ) Γ := by
  rw [prepCtx_cons]

/- ========================================================================== Typing ========================================================================== -/

inductive Typing : Ctx → Expr → Ty → Prop where
  | num (Γ : Ctx) (n : Int) : Typing Γ (Expr.num n) Ty.num
  | tru (Γ : Ctx) : Typing Γ Expr.tru Ty.bool
  | fls (Γ : Ctx) : Typing Γ Expr.fls Ty.bool
  | unit (Γ : Ctx) : Typing Γ Expr.unit Ty.unit
  | addOp (Γ : Ctx) (op : AddOp) (l r : Expr) :
      Typing Γ l Ty.num → Typing Γ r Ty.num → Typing Γ (Expr.addOp op l r) Ty.num
  | mulOp (Γ : Ctx) (op : MulOp) (l r : Expr) :
      Typing Γ l Ty.num → Typing Γ r Ty.num → Typing Γ (Expr.mulOp op l r) Ty.num
  | relOp (Γ : Ctx) (op : RelOp) (l r : Expr) :
      Typing Γ l Ty.num → Typing Γ r Ty.num → Typing Γ (Expr.relOp op l r) Ty.bool
  | and (Γ : Ctx) (l r : Expr) :
      Typing Γ l Ty.bool → Typing Γ r Ty.bool → Typing Γ (Expr.and l r) Ty.bool
  | or (Γ : Ctx) (l r : Expr) :
      Typing Γ l Ty.bool → Typing Γ r Ty.bool → Typing Γ (Expr.or l r) Ty.bool
  | if_ (Γ : Ctx) (cnd t e : Expr) (τ : Ty) :
      Typing Γ cnd Ty.bool → Typing Γ t τ → Typing Γ e τ → Typing Γ (Expr.if_ cnd t e) τ
  | var (Γ : Ctx) (i : Nat) (τ : Ty) (h : Γ i = some τ) : Typing Γ (Expr.var i) τ
  | lam (Γ : Ctx) (τ₁ : Ty) (e : Expr) (τ₂ : Ty) :
      Typing (extendCtx τ₁ Γ) e τ₂ → Typing Γ (Expr.lam τ₁ e) (Ty.fn τ₁ τ₂)
  | app (Γ : Ctx) (f a : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ f (Ty.fn τ₁ τ₂) → Typing Γ a τ₁ → Typing Γ (Expr.app f a) τ₂
  | pair (Γ : Ctx) (l r : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ l τ₁ → Typing Γ r τ₂ → Typing Γ (Expr.pair l r) (Ty.prod τ₁ τ₂)
  | projL (Γ : Ctx) (e : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ e (Ty.prod τ₁ τ₂) → Typing Γ (Expr.proj Dir.L e) τ₁
  | projR (Γ : Ctx) (e : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ e (Ty.prod τ₁ τ₂) → Typing Γ (Expr.proj Dir.R e) τ₂
  | injL (Γ : Ctx) (e : Expr) (τ τ' : Ty) :
      Typing Γ e τ → Typing Γ (Expr.inj Dir.L e) (Ty.sum τ τ')
  | injR (Γ : Ctx) (e : Expr) (τ τ' : Ty) :
      Typing Γ e τ → Typing Γ (Expr.inj Dir.R e) (Ty.sum τ' τ)
  | case_ (Γ : Ctx) (e el er : Expr) (τL τR τ : Ty) :
      Typing Γ e (Ty.sum τL τR) →
      Typing (extendCtx τL Γ) el τ → Typing (extendCtx τR Γ) er τ →
      Typing Γ (Expr.case_ e el er) τ
  | fix_ (Γ : Ctx) (τ : Ty) (e : Expr) :
      Typing (extendCtx τ Γ) e τ → Typing Γ (Expr.fix_ τ e) τ
  | let_ (Γ : Ctx) (e₁ e₂ : Expr) (τ₁ τ₂ : Ty) :
      Typing Γ e₁ τ₁ → Typing (extendCtx τ₁ Γ) e₂ τ₂ → Typing Γ (Expr.let_ e₁ e₂) τ₂

/- ========================================================================== Typing lemmas ========================================================================== -/

theorem shift_id (Δ : List Ty) (e : Expr) (τ : Ty) (d : Nat) (h : Typing (prepCtx Δ emptyCtx) e τ) : shift d Δ.length e = e := by
  revert Δ τ d h
  induction e with
  | num n => intro Δ τ d h; rfl
  | tru => intro Δ τ d h; rfl
  | fls => intro Δ τ d h; rfl
  | unit => intro Δ τ d h; rfl
  | addOp op l r ih_l ih_r =>
    intro Δ τ d h; match h with
    | Typing.addOp _ _ _ _ hl hr => simp [shift, ih_l Δ Ty.num d hl, ih_r Δ Ty.num d hr]
  | mulOp op l r ih_l ih_r =>
    intro Δ τ d h; match h with
    | Typing.mulOp _ _ _ _ hl hr => simp [shift, ih_l Δ Ty.num d hl, ih_r Δ Ty.num d hr]
  | relOp op l r ih_l ih_r =>
    intro Δ τ d h; match h with
    | Typing.relOp _ _ _ _ hl hr => simp [shift, ih_l Δ Ty.num d hl, ih_r Δ Ty.num d hr]
  | and l r ih_l ih_r =>
    intro Δ τ d h; match h with
    | Typing.and _ _ _ hl hr => simp [shift, ih_l Δ Ty.bool d hl, ih_r Δ Ty.bool d hr]
  | or l r ih_l ih_r =>
    intro Δ τ d h; match h with
    | Typing.or _ _ _ hl hr => simp [shift, ih_l Δ Ty.bool d hl, ih_r Δ Ty.bool d hr]
  | if_ c t e ih_c ih_t ih_e =>
    intro Δ τ' d h; match h with
    | Typing.if_ _ _ _ _ _ hc ht he => simp [shift, ih_c Δ Ty.bool d hc, ih_t Δ τ' d ht, ih_e Δ τ' d he]
  | var i =>
    intro Δ τ d h; match h with
    | Typing.var _ _ _ hlookup =>
      by_cases hi : i < Δ.length
      · have h_not_ge : ¬ (i ≥ Δ.length) := Nat.not_le_of_lt hi
        simp [shift, h_not_ge]
      · have h_ge : i ≥ Δ.length := Nat.ge_of_not_lt hi
        have hpos : prepCtx Δ emptyCtx i = emptyCtx (i - Δ.length) := prepCtx_lookup_ge Δ emptyCtx i h_ge
        rw [hpos] at hlookup; simp [emptyCtx] at hlookup
  | lam σ body ih_body =>
    intro Δ τ d h; match h with
    | Typing.lam _ _ _ τ₂ hb =>
      have h_ctx : extendCtx σ (prepCtx Δ emptyCtx) = prepCtx (σ :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx] at hb
      have h_ih := ih_body (σ :: Δ) τ₂ d hb
      have h_len : (σ :: Δ).length = Δ.length + 1 := by simp
      rw [h_len] at h_ih; simp [shift, h_ih]
  | app f a ih_f ih_a =>
    intro Δ τ d h; match h with
    | Typing.app _ _ _ τ₁ τ₂ hf ha => simp [shift, ih_f Δ (Ty.fn τ₁ τ₂) d hf, ih_a Δ τ₁ d ha]
  | pair l r ih_l ih_r =>
    intro Δ τ d h; match h with
    | Typing.pair _ _ _ τ₁ τ₂ hl hr => simp [shift, ih_l Δ τ₁ d hl, ih_r Δ τ₂ d hr]
  | proj dir e ih_e =>
    intro Δ τ d h; match h with
    | Typing.projL _ _ τ₁ τ₂ he => simp [shift, ih_e Δ (Ty.prod τ₁ τ₂) d he]
    | Typing.projR _ _ τ₁ τ₂ he => simp [shift, ih_e Δ (Ty.prod τ₁ τ₂) d he]
  | inj dir e ih_e =>
    intro Δ τ d h; match h with
    | Typing.injL _ _ _ _ he => simp [shift, ih_e Δ _ d he]
    | Typing.injR _ _ _ _ he => simp [shift, ih_e Δ _ d he]
  | case_ e el er ih_e ih_el ih_er =>
    intro Δ τ d h; match h with
    | Typing.case_ _ _ _ _ τL τR _ hse hel her =>
      have h_ctx_l : extendCtx τL (prepCtx Δ emptyCtx) = prepCtx (τL :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      have h_ctx_r : extendCtx τR (prepCtx Δ emptyCtx) = prepCtx (τR :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx_l] at hel; rw [h_ctx_r] at her
      have h_ih_el := ih_el (τL :: Δ) τ d hel
      have h_ih_er := ih_er (τR :: Δ) τ d her
      have h_len_l : (τL :: Δ).length = Δ.length + 1 := by simp
      have h_len_r : (τR :: Δ).length = Δ.length + 1 := by simp
      rw [h_len_l] at h_ih_el; rw [h_len_r] at h_ih_er
      simp [shift, ih_e Δ (Ty.sum τL τR) d hse, h_ih_el, h_ih_er]
  | fix_ σ body ih_body =>
    intro Δ τ d h; match h with
    | Typing.fix_ _ _ _ he =>
      have h_ctx : extendCtx σ (prepCtx Δ emptyCtx) = prepCtx (σ :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx] at he
      have h_ih := ih_body (σ :: Δ) σ d he
      have h_len : (σ :: Δ).length = Δ.length + 1 := by simp
      rw [h_len] at h_ih; simp [shift, h_ih]
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro Δ τ d h; match h with
    | Typing.let_ _ _ _ τ₁ τ₂ h₁ h₂ =>
      have h_ctx : extendCtx τ₁ (prepCtx Δ emptyCtx) = prepCtx (τ₁ :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx] at h₂
      have h_ih₂ := ih₂ (τ₁ :: Δ) τ₂ d h₂
      have h_len : (τ₁ :: Δ).length = Δ.length + 1 := by simp
      rw [h_len] at h_ih₂; simp [shift, ih₁ Δ τ₁ d h₁, h_ih₂]

theorem weaken_prep (Δ : List Ty) (Γ : Ctx) (e : Expr) (τ : Ty) (h : Typing (prepCtx Δ emptyCtx) e τ) : Typing (prepCtx Δ Γ) e τ := by
  revert Δ Γ τ h
  induction e with
  | num n => intro Δ Γ τ h; cases h; exact Typing.num (prepCtx Δ Γ) n
  | tru => intro Δ Γ τ h; cases h; exact Typing.tru (prepCtx Δ Γ)
  | fls => intro Δ Γ τ h; cases h; exact Typing.fls (prepCtx Δ Γ)
  | unit => intro Δ Γ τ h; cases h; exact Typing.unit (prepCtx Δ Γ)
  | addOp op l r ih_l ih_r =>
    intro Δ Γ τ h; match h with
    | Typing.addOp _ _ _ _ hl hr =>
      exact Typing.addOp (prepCtx Δ Γ) op _ _ (ih_l Δ Γ Ty.num hl) (ih_r Δ Γ Ty.num hr)
  | mulOp op l r ih_l ih_r =>
    intro Δ Γ τ h; match h with
    | Typing.mulOp _ _ _ _ hl hr =>
      exact Typing.mulOp (prepCtx Δ Γ) op _ _ (ih_l Δ Γ Ty.num hl) (ih_r Δ Γ Ty.num hr)
  | relOp op l r ih_l ih_r =>
    intro Δ Γ τ h; match h with
    | Typing.relOp _ _ _ _ hl hr =>
      exact Typing.relOp (prepCtx Δ Γ) op _ _ (ih_l Δ Γ Ty.num hl) (ih_r Δ Γ Ty.num hr)
  | and l r ih_l ih_r =>
    intro Δ Γ τ h; match h with
    | Typing.and _ _ _ hl hr =>
      exact Typing.and (prepCtx Δ Γ) _ _ (ih_l Δ Γ Ty.bool hl) (ih_r Δ Γ Ty.bool hr)
  | or l r ih_l ih_r =>
    intro Δ Γ τ h; match h with
    | Typing.or _ _ _ hl hr =>
      exact Typing.or (prepCtx Δ Γ) _ _ (ih_l Δ Γ Ty.bool hl) (ih_r Δ Γ Ty.bool hr)
  | if_ c t e ih_c ih_t ih_e =>
    intro Δ Γ τ h; match h with
    | Typing.if_ _ _ _ _ τ' hc ht he =>
      exact Typing.if_ (prepCtx Δ Γ) _ _ _ τ' (ih_c Δ Γ Ty.bool hc) (ih_t Δ Γ τ' ht) (ih_e Δ Γ τ' he)
  | var i =>
    intro Δ Γ τ h; match h with
    | Typing.var _ _ _ hlookup =>
      by_cases hi : i < Δ.length
      · have hpos_Γ : prepCtx Δ Γ i = some (Δ.get ⟨i, hi⟩) := prepCtx_lookup_lt Δ Γ i hi
        have hpos_empty : prepCtx Δ emptyCtx i = some (Δ.get ⟨i, hi⟩) := prepCtx_lookup_lt Δ emptyCtx i hi
        rw [hpos_empty] at hlookup; simp at hlookup; subst hlookup
        exact Typing.var (prepCtx Δ Γ) i (Δ.get ⟨i, hi⟩) hpos_Γ
      · have h_ge : i ≥ Δ.length := Nat.ge_of_not_lt hi
        have hpos_empty : prepCtx Δ emptyCtx i = emptyCtx (i - Δ.length) := prepCtx_lookup_ge Δ emptyCtx i h_ge
        rw [hpos_empty] at hlookup; simp [emptyCtx] at hlookup
  | lam σ body ih_body =>
    intro Δ Γ τ h; match h with
    | Typing.lam _ _ _ τ₂ hb =>
      have h_ctx : extendCtx σ (prepCtx Δ emptyCtx) = prepCtx (σ :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx] at hb
      have h_ih := ih_body (σ :: Δ) Γ τ₂ hb
      have h_ctx' : prepCtx (σ :: Δ) Γ = extendCtx σ (prepCtx Δ Γ) := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx'] at h_ih
      exact Typing.lam (prepCtx Δ Γ) σ body τ₂ h_ih
  | app f a ih_f ih_a =>
    intro Δ Γ τ h; match h with
    | Typing.app _ _ _ τ₁ τ₂ hf ha =>
      exact Typing.app (prepCtx Δ Γ) _ _ τ₁ τ₂ (ih_f Δ Γ (Ty.fn τ₁ τ₂) hf) (ih_a Δ Γ τ₁ ha)
  | pair l r ih_l ih_r =>
    intro Δ Γ τ h; match h with
    | Typing.pair _ _ _ τ₁ τ₂ hl hr =>
      exact Typing.pair (prepCtx Δ Γ) _ _ τ₁ τ₂ (ih_l Δ Γ τ₁ hl) (ih_r Δ Γ τ₂ hr)
  | proj dir e ih_e =>
    intro Δ Γ τ h; match h with
    | Typing.projL _ _ τ₁ τ₂ he => exact Typing.projL (prepCtx Δ Γ) _ τ₁ τ₂ (ih_e Δ Γ (Ty.prod τ₁ τ₂) he)
    | Typing.projR _ _ τ₁ τ₂ he => exact Typing.projR (prepCtx Δ Γ) _ τ₁ τ₂ (ih_e Δ Γ (Ty.prod τ₁ τ₂) he)
  | inj dir e ih_e =>
    intro Δ Γ τ h; match h with
    | Typing.injL _ _ _ _ he => exact Typing.injL (prepCtx Δ Γ) _ _ _ (ih_e Δ Γ _ he)
    | Typing.injR _ _ _ _ he => exact Typing.injR (prepCtx Δ Γ) _ _ _ (ih_e Δ Γ _ he)
  | case_ e el er ih_e ih_el ih_er =>
    intro Δ Γ τ h; match h with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her =>
      have h_ctx_l : extendCtx τL (prepCtx Δ emptyCtx) = prepCtx (τL :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      have h_ctx_r : extendCtx τR (prepCtx Δ emptyCtx) = prepCtx (τR :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx_l] at hel; rw [h_ctx_r] at her
      have h_ih_el := ih_el (τL :: Δ) Γ τ' hel
      have h_ih_er := ih_er (τR :: Δ) Γ τ' her
      have h_ctx_l' : prepCtx (τL :: Δ) Γ = extendCtx τL (prepCtx Δ Γ) := by rw [extendCtx_prepCtx_comm]
      have h_ctx_r' : prepCtx (τR :: Δ) Γ = extendCtx τR (prepCtx Δ Γ) := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx_l'] at h_ih_el
      rw [h_ctx_r'] at h_ih_er
      exact Typing.case_ (prepCtx Δ Γ) _ _ _ τL τR τ' (ih_e Δ Γ (Ty.sum τL τR) hse) h_ih_el h_ih_er
  | fix_ σ body ih_body =>
    intro Δ Γ τ h; match h with
    | Typing.fix_ _ _ _ he =>
      have h_ctx : extendCtx σ (prepCtx Δ emptyCtx) = prepCtx (σ :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx] at he
      have h_ih := ih_body (σ :: Δ) Γ σ he
      have h_ctx' : prepCtx (σ :: Δ) Γ = extendCtx σ (prepCtx Δ Γ) := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx'] at h_ih
      exact Typing.fix_ (prepCtx Δ Γ) σ body h_ih
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro Δ Γ τ h; match h with
    | Typing.let_ _ _ _ τ₁ τ₂ h₁ h₂ =>
      have h_ctx : extendCtx τ₁ (prepCtx Δ emptyCtx) = prepCtx (τ₁ :: Δ) emptyCtx := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx] at h₂
      have h_ih₂ := ih₂ (τ₁ :: Δ) Γ τ₂ h₂
      have h_ctx' : prepCtx (τ₁ :: Δ) Γ = extendCtx τ₁ (prepCtx Δ Γ) := by rw [extendCtx_prepCtx_comm]
      rw [h_ctx'] at h_ih₂
      exact Typing.let_ (prepCtx Δ Γ) _ _ τ₁ τ₂ (ih₁ Δ Γ τ₁ h₁) h_ih₂

theorem closed_any_ctx (Γ : Ctx) (e : Expr) (τ : Ty) (h : Typing emptyCtx e τ) : Typing Γ e τ := by
  have := weaken_prep [] Γ e τ (by simpa [prepCtx_nil] using h)
  simpa [prepCtx_nil] using this

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

/- ========================================================================== Substitution lemma ========================================================================== -/

theorem list_get_append_lt (Δ : List Ty) (τ : Ty) (i : Nat) (h : i < Δ.length) :
    (Δ ++ [τ]).get ⟨i, Nat.lt_of_lt_of_le h (by simp)⟩ = Δ.get ⟨i, h⟩ := by
  induction Δ generalizing i with
  | nil => exact (Nat.not_lt_zero _ h).elim
  | cons σ Δ' ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < Δ'.length := Nat.lt_of_succ_lt_succ h
      simpa [List.get] using ih i h'

theorem list_get_append_last (Δ : List Ty) (τ : Ty) (h : Δ.length < (Δ ++ [τ]).length) :
    (Δ ++ [τ]).get ⟨Δ.length, h⟩ = τ := by
  induction Δ with
  | nil => rfl
  | cons _ Δ' ih =>
    have h' : Δ'.length < (Δ' ++ [τ]).length := by
      rw [List.length_append]; exact Nat.lt_succ_self _
    have hfin : (⟨Δ'.length, Nat.lt_of_succ_lt_succ h⟩ : Fin (Δ' ++ [τ]).length) =
        (⟨Δ'.length, h'⟩ : Fin (Δ' ++ [τ]).length) := by
      ext; rfl
    simpa [List.get, hfin] using ih h'

theorem get_append_left (as bs : List Ty) (i : Nat) (h : i < as.length) : (as ++ bs)[i]'(by
    have hi : i < (as ++ bs).length := by
      rw [List.length_append]
      exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
    exact hi) = as[i] := by
  induction as generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons a as ih =>
    cases i with
    | zero => rfl
     | succ i' =>
      simp
      apply ih

theorem subst_typing_gen (Δ : List Ty) (body : Expr) (τ τ_out : Ty)
    (h_body : Typing (prepCtx (Δ ++ [τ]) emptyCtx) body τ_out) (s : Expr) (h_s : Typing emptyCtx s τ) :
    Typing (prepCtx Δ emptyCtx) (subst Δ.length s body) τ_out := by
  revert Δ τ τ_out h_body s h_s
  induction body with
  | num n => intro Δ τ τ_out h_body s h_s; cases h_body; simp [subst]; exact Typing.num (prepCtx Δ emptyCtx) n
  | tru => intro Δ τ τ_out h_body s h_s; cases h_body; simp [subst]; exact Typing.tru (prepCtx Δ emptyCtx)
  | fls => intro Δ τ τ_out h_body s h_s; cases h_body; simp [subst]; exact Typing.fls (prepCtx Δ emptyCtx)
  | unit => intro Δ τ τ_out h_body s h_s; cases h_body; simp [subst]; exact Typing.unit (prepCtx Δ emptyCtx)
  | addOp op l r ih_l ih_r =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.addOp _ _ _ _ hl hr =>
      simp [subst]; exact Typing.addOp (prepCtx Δ emptyCtx) op _ _ (ih_l Δ τ Ty.num hl s h_s) (ih_r Δ τ Ty.num hr s h_s)
  | mulOp op l r ih_l ih_r =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.mulOp _ _ _ _ hl hr =>
      simp [subst]; exact Typing.mulOp (prepCtx Δ emptyCtx) op _ _ (ih_l Δ τ Ty.num hl s h_s) (ih_r Δ τ Ty.num hr s h_s)
  | relOp op l r ih_l ih_r =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.relOp _ _ _ _ hl hr =>
      simp [subst]; exact Typing.relOp (prepCtx Δ emptyCtx) op _ _ (ih_l Δ τ Ty.num hl s h_s) (ih_r Δ τ Ty.num hr s h_s)
  | and l r ih_l ih_r =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.and _ _ _ hl hr =>
      simp [subst]; exact Typing.and (prepCtx Δ emptyCtx) _ _ (ih_l Δ τ Ty.bool hl s h_s) (ih_r Δ τ Ty.bool hr s h_s)
  | or l r ih_l ih_r =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.or _ _ _ hl hr =>
      simp [subst]; exact Typing.or (prepCtx Δ emptyCtx) _ _ (ih_l Δ τ Ty.bool hl s h_s) (ih_r Δ τ Ty.bool hr s h_s)
  | if_ c t e ih_c ih_t ih_e =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.if_ _ _ _ _ τ' hc ht he =>
      simp [subst]; exact Typing.if_ (prepCtx Δ emptyCtx) _ _ _ τ' (ih_c Δ τ Ty.bool hc s h_s) (ih_t Δ τ τ' ht s h_s) (ih_e Δ τ τ' he s h_s)
  | var i =>
    intro Δ τ τ_out h_body s h_s
    cases h_body; rename_i hlookup
    by_cases hi_lt_k : i < Δ.length
    · simp [subst, hi_lt_k]
      -- hlookup : prepCtx (Δ ++ [τ]) emptyCtx i = some τ_out
      -- Need: Typing (prepCtx Δ emptyCtx) (var i) τ_out
      -- Since i < Δ.length, both contexts give the same type (Δ[i])
      have h_lookup_Δ : prepCtx Δ emptyCtx i = some τ_out := by
        have hi_all : i < (Δ ++ [τ]).length := by
          rw [List.length_append]; exact Nat.lt_of_lt_of_le hi_lt_k (by simp)
        -- From hlookup using prepCtx_lookup_lt on (Δ ++ [τ])
        rw [prepCtx_lookup_lt (Δ ++ [τ]) emptyCtx i hi_all] at hlookup
        -- hlookup : some ((Δ ++ [τ]).get ⟨i, hi_all⟩) = some τ_out
        have h_elem : (Δ ++ [τ])[i] = Δ[i] := by
          have hi_append : i < (Δ ++ [τ]).length := by
            rw [List.length_append]; exact Nat.lt_of_lt_of_le hi_lt_k (Nat.le_add_right _ _)
          have htemp := get_append_left Δ [τ] i hi_lt_k
          simpa using htemp
        -- Rewrite the get notation to bracket notation in hlookup
        have hlookup' : some ((Δ ++ [τ])[i]) = some τ_out := by simpa using hlookup
        rw [h_elem] at hlookup'
        -- Now hlookup' : some (Δ[i]) = some τ_out
        -- Also rewrite prepCtx_lookup_lt to relate Δ[i] with prepCtx
        have h_prep : prepCtx Δ emptyCtx i = some (Δ.get ⟨i, hi_lt_k⟩) := prepCtx_lookup_lt Δ emptyCtx i hi_lt_k
        -- Δ[i] is notation for Δ.get ⟨i, hi_lt_k⟩, but they're syntactically different
        -- So use simpa with the prepCtx lemma
        simpa [h_prep] using hlookup'
      exact Typing.var (prepCtx Δ emptyCtx) i τ_out h_lookup_Δ
    · by_cases hi_eq_k : i = Δ.length
      · subst hi_eq_k; simp [subst, hi_lt_k]
        have h_tau : τ_out = τ := by
          have hlen : Δ.length < (Δ ++ [τ]).length := by
            rw [List.length_append]; simp
          have hpos : prepCtx (Δ ++ [τ]) emptyCtx Δ.length = some τ := by
            rw [prepCtx_lookup_lt (Δ ++ [τ]) emptyCtx Δ.length hlen]
            simp
          rw [hpos] at hlookup; simp at hlookup; exact hlookup.symm
        rw [h_tau]
        have h_shift_eq : shift Δ.length 0 s = s := by
          have h_prep : Typing (prepCtx [] emptyCtx) s τ := by simpa [prepCtx_nil] using h_s
          have htemp := shift_id [] s τ Δ.length h_prep
          simpa using htemp
        rw [h_shift_eq]
        exact closed_any_ctx (prepCtx Δ emptyCtx) s τ h_s
      · have hi_gt_k : Δ.length < i := Nat.lt_of_le_of_ne (Nat.ge_of_not_lt hi_lt_k) (Ne.symm hi_eq_k)
        simp [subst, hi_lt_k, hi_eq_k]
        have hpos : prepCtx (Δ ++ [τ]) emptyCtx i = emptyCtx (i - (Δ ++ [τ]).length) :=
          prepCtx_lookup_ge (Δ ++ [τ]) emptyCtx i (by rw [List.length_append]; exact Nat.succ_le_of_lt hi_gt_k)
        rw [hpos] at hlookup; simp [emptyCtx] at hlookup
  | lam σ body' ih_body =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.lam _ _ _ τ₂ hb =>
      have h_ctx : extendCtx σ (prepCtx (Δ ++ [τ]) emptyCtx) = prepCtx ((σ :: Δ) ++ [τ]) emptyCtx := by
        rw [extendCtx_prepCtx_comm]; simp
      rw [h_ctx] at hb
      have h_ih := ih_body (σ :: Δ) τ τ₂ hb s h_s
      have h_len : (σ :: Δ).length = Δ.length + 1 := by simp
      have h_prep : prepCtx (σ :: Δ) emptyCtx = extendCtx σ (prepCtx Δ emptyCtx) := by rw [extendCtx_prepCtx_comm]
      rw [h_len, h_prep] at h_ih; simp [subst]
      exact Typing.lam (prepCtx Δ emptyCtx) σ (subst (Δ.length + 1) s body') τ₂ h_ih
  | app f a ih_f ih_a =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.app _ _ _ τ₁ τ₂ hf ha =>
      simp [subst]; exact Typing.app (prepCtx Δ emptyCtx) _ _ τ₁ τ₂ (ih_f Δ τ (Ty.fn τ₁ τ₂) hf s h_s) (ih_a Δ τ τ₁ ha s h_s)
  | pair l r ih_l ih_r =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.pair _ _ _ τ₁ τ₂ hl hr =>
      simp [subst]; exact Typing.pair (prepCtx Δ emptyCtx) _ _ τ₁ τ₂ (ih_l Δ τ τ₁ hl s h_s) (ih_r Δ τ τ₂ hr s h_s)
  | proj d e ih_e =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.projL _ _ τ₁ τ₂ he => simp [subst]; exact Typing.projL (prepCtx Δ emptyCtx) _ τ₁ τ₂ (ih_e Δ τ (Ty.prod τ₁ τ₂) he s h_s)
    | Typing.projR _ _ τ₁ τ₂ he => simp [subst]; exact Typing.projR (prepCtx Δ emptyCtx) _ τ₁ τ₂ (ih_e Δ τ (Ty.prod τ₁ τ₂) he s h_s)
  | inj d e ih_e =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.injL _ _ _ σ he => simp [subst]; exact Typing.injL (prepCtx Δ emptyCtx) _ _ σ (ih_e Δ τ _ he s h_s)
    | Typing.injR _ _ _ σ he => simp [subst]; exact Typing.injR (prepCtx Δ emptyCtx) _ _ σ (ih_e Δ τ _ he s h_s)
  | case_ e el er ih_e ih_el ih_er =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her =>
      have h_ctx_l : extendCtx τL (prepCtx (Δ ++ [τ]) emptyCtx) = prepCtx ((τL :: Δ) ++ [τ]) emptyCtx := by
        rw [extendCtx_prepCtx_comm]; simp
      have h_ctx_r : extendCtx τR (prepCtx (Δ ++ [τ]) emptyCtx) = prepCtx ((τR :: Δ) ++ [τ]) emptyCtx := by
        rw [extendCtx_prepCtx_comm]; simp
      rw [h_ctx_l] at hel; rw [h_ctx_r] at her
      have h_ih_el := ih_el (τL :: Δ) τ τ' hel s h_s
      have h_ih_er := ih_er (τR :: Δ) τ τ' her s h_s
      have h_len_l : (τL :: Δ).length = Δ.length + 1 := by simp
      have h_len_r : (τR :: Δ).length = Δ.length + 1 := by simp
      have h_prep_l : prepCtx (τL :: Δ) emptyCtx = extendCtx τL (prepCtx Δ emptyCtx) := by rw [extendCtx_prepCtx_comm]
      have h_prep_r : prepCtx (τR :: Δ) emptyCtx = extendCtx τR (prepCtx Δ emptyCtx) := by rw [extendCtx_prepCtx_comm]
      rw [h_len_l, h_prep_l] at h_ih_el
      rw [h_len_r, h_prep_r] at h_ih_er
      simp [subst]
      exact Typing.case_ (prepCtx Δ emptyCtx) _ _ _ τL τR τ' (ih_e Δ τ (Ty.sum τL τR) hse s h_s) h_ih_el h_ih_er
  | fix_ σ body' ih_body =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.fix_ _ _ _ he =>
      have h_ctx : extendCtx σ (prepCtx (Δ ++ [τ]) emptyCtx) = prepCtx ((σ :: Δ) ++ [τ]) emptyCtx := by
        rw [extendCtx_prepCtx_comm]; simp
      rw [h_ctx] at he
      have h_ih := ih_body (σ :: Δ) τ σ he s h_s
      have h_len : (σ :: Δ).length = Δ.length + 1 := by simp
      have h_prep : prepCtx (σ :: Δ) emptyCtx = extendCtx σ (prepCtx Δ emptyCtx) := by rw [extendCtx_prepCtx_comm]
      rw [h_len, h_prep] at h_ih; simp [subst]
      exact Typing.fix_ (prepCtx Δ emptyCtx) σ (subst (Δ.length + 1) s body') h_ih
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro Δ τ τ_out h_body s h_s; match h_body with
    | Typing.let_ _ _ _ τ₁ τ₂ h₁ h₂ =>
      have h_ctx : extendCtx τ₁ (prepCtx (Δ ++ [τ]) emptyCtx) = prepCtx ((τ₁ :: Δ) ++ [τ]) emptyCtx := by
        rw [extendCtx_prepCtx_comm]; simp
      rw [h_ctx] at h₂
      have h_ih₂ := ih₂ (τ₁ :: Δ) τ τ₂ h₂ s h_s
      have h_len : (τ₁ :: Δ).length = Δ.length + 1 := by simp
      have h_prep : prepCtx (τ₁ :: Δ) emptyCtx = extendCtx τ₁ (prepCtx Δ emptyCtx) := by rw [extendCtx_prepCtx_comm]
      rw [h_len, h_prep] at h_ih₂; simp [subst]
      exact Typing.let_ (prepCtx Δ emptyCtx) _ _ τ₁ τ₂ (ih₁ Δ τ τ₁ h₁ s h_s) h_ih₂

theorem subst_typing (body s : Expr) (τ τ_out : Ty)
    (h_body : Typing (extendCtx τ emptyCtx) body τ_out) (h_s : Typing emptyCtx s τ) : Typing emptyCtx (subst 0 s body) τ_out := by
  have h_prep : extendCtx τ emptyCtx = prepCtx ([] ++ [τ]) emptyCtx := by simp [prepCtx_nil, prepCtx_one]
  rw [h_prep] at h_body
  have h := subst_typing_gen [] body τ τ_out h_body s h_s
  simp at h; exact h

/- ========================================================================== Canonical forms ========================================================================== -/

theorem canonical_num (e : Expr) (hv : Value e) (ht : Typing emptyCtx e Ty.num) : ∃ n : Int, e = Expr.num n := by
  cases hv
  case num => rename_i n; exact ⟨n, rfl⟩
  case var => cases ht; rename_i _ h; simp [emptyCtx] at h
  all_goals { cases ht }

theorem canonical_bool (e : Expr) (hv : Value e) (ht : Typing emptyCtx e Ty.bool) : e = Expr.tru ∨ e = Expr.fls := by
  cases hv
  case tru => exact Or.inl rfl
  case fls => exact Or.inr rfl
  case var => cases ht; rename_i _ h; simp [emptyCtx] at h
  all_goals { cases ht }

theorem canonical_fn (e : Expr) (hv : Value e) (ht : Typing emptyCtx e (Ty.fn τ₁ τ₂)) : ∃ (σ : Ty) (b : Expr), e = Expr.lam σ b := by
  cases hv
  case lam => rename_i σ b; exact ⟨σ, b, rfl⟩
  case var => cases ht; rename_i _ h; simp [emptyCtx] at h
  all_goals { cases ht }

theorem canonical_prod (e : Expr) (hv : Value e) (ht : Typing emptyCtx e (Ty.prod τ₁ τ₂)) : ∃ l r : Expr, e = Expr.pair l r := by
  cases hv
  case pair => rename_i l r; exact ⟨l, r, rfl⟩
  case var => cases ht; rename_i _ h; simp [emptyCtx] at h
  all_goals { cases ht }

theorem canonical_sum (e : Expr) (hv : Value e) (ht : Typing emptyCtx e (Ty.sum τ₁ τ₂)) : ∃ (d : Dir) (v : Expr), e = Expr.inj d v := by
  cases hv
  case inj => rename_i d v; exact ⟨d, v, rfl⟩
  case var => cases ht; rename_i _ h; simp [emptyCtx] at h
  all_goals { cases ht }

/- ========================================================================== Progress ========================================================================== -/

theorem progress (e : Expr) (τ : Ty) (h : Typing emptyCtx e τ) : Value e ∨ ∃ e', Step e e' := by
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
    | Typing.var _ _ _ hlookup => simp [emptyCtx] at hlookup
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

/- ========================================================================== Preservation ========================================================================== -/

theorem preservation (e e' : Expr) (τ : Ty) (h : Typing emptyCtx e τ) (hstep : Step e e') : Typing emptyCtx e' τ := by
  induction hstep generalizing τ with
  | addL op e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.addOp _ _ _ _ hl hr => exact Typing.addOp emptyCtx op _ _ (ih Ty.num hl) hr
  | addR op v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.addOp _ _ _ _ hl hr => exact Typing.addOp emptyCtx op _ _ hl (ih Ty.num hr)
  | addAdd n₁ n₂ =>
    match h with
    | Typing.addOp _ _ _ _ _ _ => exact Typing.num emptyCtx (n₁ + n₂)
  | addSub n₁ n₂ =>
    match h with
    | Typing.addOp _ _ _ _ _ _ => exact Typing.num emptyCtx (n₁ - n₂)
  | mulL op e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.mulOp _ _ _ _ hl hr => exact Typing.mulOp emptyCtx op _ _ (ih Ty.num hl) hr
  | mulR op v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.mulOp _ _ _ _ hl hr => exact Typing.mulOp emptyCtx op _ _ hl (ih Ty.num hr)
  | mulMul n₁ n₂ =>
    match h with
    | Typing.mulOp _ _ _ _ _ _ => exact Typing.num emptyCtx (n₁ * n₂)
  | mulDiv n₁ n₂ =>
    match h with
    | Typing.mulOp _ _ _ _ _ _ => exact Typing.num emptyCtx (n₁ / n₂)
  | relL op e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.relOp _ _ _ _ hl hr => exact Typing.relOp emptyCtx op _ _ (ih Ty.num hl) hr
  | relR op v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.relOp _ _ _ _ hl hr => exact Typing.relOp emptyCtx op _ _ hl (ih Ty.num hr)
  | relLtT n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.tru emptyCtx
  | relLtF n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.fls emptyCtx
  | relGtT n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.tru emptyCtx
  | relGtF n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.fls emptyCtx
  | relEqT n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.tru emptyCtx
  | relEqF n₁ n₂ _ =>
    match h with
    | Typing.relOp _ _ _ _ _ _ => exact Typing.fls emptyCtx
  | andL e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.and _ _ _ hl hr => exact Typing.and emptyCtx _ _ (ih Ty.bool hl) hr
  | andTrue e₂ =>
    match h with
    | Typing.and _ _ _ _ hr => exact hr
  | andFalse e₂ =>
    match h with
    | Typing.and _ _ _ _ _ => exact Typing.fls emptyCtx
  | orL e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.or _ _ _ hl hr => exact Typing.or emptyCtx _ _ (ih Ty.bool hl) hr
  | orTrue e₂ =>
    match h with
    | Typing.or _ _ _ _ _ => exact Typing.tru emptyCtx
  | orFalse e₂ =>
    match h with
    | Typing.or _ _ _ _ hr => exact hr
  | ifL c c' t e hstep' ih =>
    match h with
    | Typing.if_ _ _ _ _ τ' hc ht he => exact Typing.if_ emptyCtx _ _ _ τ' (ih Ty.bool hc) ht he
  | ifTrue t e =>
    match h with
    | Typing.if_ _ _ _ _ _ _ ht _ => exact ht
  | ifFalse t e =>
    match h with
    | Typing.if_ _ _ _ _ _ _ _ he => exact he
  | appL e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.app _ _ _ τ₁ τ₂ hf ha => exact Typing.app emptyCtx _ _ τ₁ τ₂ (ih (Ty.fn τ₁ τ₂) hf) ha
  | appR v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.app _ _ _ τ₁ τ₂ hf ha => exact Typing.app emptyCtx _ _ τ₁ τ₂ hf (ih τ₁ ha)
  | appLam τ₁ body v hv =>
    match h with
    | Typing.app _ _ _ _ τ₂ hf ha =>
      match hf with
      | Typing.lam _ _ _ _ hb => exact subst_typing body v τ₁ τ₂ hb ha
  | pairL e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.pair _ _ _ τ₁ τ₂ hl hr => exact Typing.pair emptyCtx _ _ τ₁ τ₂ (ih τ₁ hl) hr
  | pairR v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.pair _ _ _ τ₁ τ₂ hl hr => exact Typing.pair emptyCtx _ _ τ₁ τ₂ hl (ih τ₂ hr)
  | proj_step e e' d hstep' ih =>
    match h with
    | Typing.projL _ _ τ₁ τ₂ he => exact Typing.projL emptyCtx _ τ₁ τ₂ (ih (Ty.prod τ₁ τ₂) he)
    | Typing.projR _ _ τ₁ τ₂ he => exact Typing.projR emptyCtx _ τ₁ τ₂ (ih (Ty.prod τ₁ τ₂) he)
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
    | Typing.injL _ _ τ τ' he => exact Typing.injL emptyCtx _ τ τ' (ih τ he)
    | Typing.injR _ _ τ τ' he => exact Typing.injR emptyCtx _ τ τ' (ih τ he)
  | case_step e e' el er hstep' ih =>
    match h with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her => exact Typing.case_ emptyCtx _ _ _ τL τR τ' (ih (Ty.sum τL τR) hse) hel her
  | caseL_val v el er =>
    match h with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her =>
      match hse with
      | Typing.injL _ _ _ _ hv_ty => exact subst_typing el v τL τ' hel hv_ty
  | caseR_val v el er =>
    match h with
    | Typing.case_ _ _ _ _ τL τR τ' hse hel her =>
      match hse with
      | Typing.injR _ _ _ _ hv_ty => exact subst_typing er v τR τ' her hv_ty
  | fix_step τ₁ body =>
    match h with
    | Typing.fix_ _ _ _ hb => exact subst_typing body (Expr.fix_ τ₁ body) τ₁ τ₁ hb (Typing.fix_ emptyCtx τ₁ body hb)
  | let_step e₁ e₁' e₂ hstep' ih =>
    match h with
    | Typing.let_ _ _ _ τ₁ τ₂ h₁ h₂ => exact Typing.let_ emptyCtx _ _ τ₁ τ₂ (ih τ₁ h₁) h₂
  | let_val v e₂ hv =>
    match h with
    | Typing.let_ _ _ _ τ₁ τ₂ h₁ h₂ => exact subst_typing e₂ v τ₁ τ₂ h₂ h₁
