import tactic

structure graph := (V : ℕ)
  (E : ℕ → ℕ → bool)
  (E_irreflexive : ∀ x : ℕ, x < V → ¬ E x x)
  (E_symmetric : ∀ x y : ℕ, x < V → y < V → E x y → E y x)

def K (n: ℕ): graph := begin
  refine_struct ({
    V := n, 
    E := (λ x, λ y, x ≠ y),
  }),
  simp,
  intros,
  cc,
end

def Path (n: ℕ): graph := begin
  refine_struct ({
    V := n, 
    E := (λ x, λ y, nat.succ x = y ∨ x = nat.succ y),
  }),
  simp,
  intros,
  omega,
  simp,
  tauto,
end

def Empty (n: ℕ): graph := begin
  refine_struct ({
    V := n, 
    E := (λ x, λ y, false),
  }),
  tauto,
  tauto,
end

def sum_fun : (ℕ → ℕ) -> ℕ → ℕ
| m 0 := 0
| m (n + 1) := m n + sum_fun m n

notation `∑` binders ` to ` n `, ` r:(scoped:67 f, sum_fun f n) := r
-- this means `∑ x to n, foo` denotes `sum_fun (λ x, foo) n`
-- the `∑` is entered using \sum

def edges (G : graph) : ℕ :=
∑ x to G.V, ∑ y to x, if G.E x y then 1 else 0

def degree (G : graph) (x : ℕ) : ℕ :=
∑ y to G.V, if G.E x y then 1 else 0

def darts (G : graph) : ℕ :=
∑ x to G.V, ∑ y to G.V, if G.E x y then 1 else 0

@[simp]
lemma sum_to_zero_eq (f : ℕ → ℕ) : ∑ x to 0, f x = 0 := rfl

@[simp]
lemma sum_zero_eq (n : ℕ) : ∑ x to n, 0 = 0 :=
begin
  induction n,
  rw sum_to_zero_eq,
  dunfold sum_fun,
  rw n_ih,
end

lemma sum_add_eq_add_sum (f g : ℕ → ℕ) (n : ℕ) :
  ∑ x to n, (f x + g x) = ∑ x to n, f x + ∑ x to n, g x :=
begin
  induction n,
  { simp, },
  { dunfold sum_fun,
    rw n_ih,
    ring, }
end

lemma sum_if_true (f g : ℕ → ℕ) (p : ℕ → Prop) [decidable_pred p] (n : ℕ) (h : ∀ x, x < n → p x) :
  ∑ x to n, (if p x then f x else g x) = ∑ x to n, f x :=
begin
  induction n,
  { simp },
  { dunfold sum_fun,
    have k := h n_n (lt_add_one _),
    simp [k],
    rw n_ih,
    intros x hlt, apply h, exact nat.lt.step hlt, }
end

lemma sum_if_false (f g : ℕ → ℕ) (p : ℕ → Prop) [decidable_pred p] (n : ℕ) (h : ∀ x, x < n → ¬ p x) :
  ∑ x to n, (if p x then f x else g x) = ∑ x to n, g x :=
begin
  induction n,
  { simp },
  { dunfold sum_fun,
    have k := h n_n (lt_add_one _),
    simp [k],
    rw n_ih,
    intros x hlt, apply h, exact nat.lt.step hlt, }
end

lemma sum_fun_restrict' (f : ℕ → ℕ) (n m : ℕ) :
  ∑ x to n, f x = ∑ x to n + m, if x < n then f x else 0 :=
begin
  induction m,
  { rw sum_if_true,
    simp, simp, },
  { rw nat.add_succ,
    dunfold sum_fun,
    rw ←m_ih,
    split_ifs,
    exfalso, linarith,
    simp, },
end

lemma sum_fun_restrict (f : ℕ → ℕ) (n m : ℕ) (h : n ≤ m) :
  ∑ x to n, f x = ∑ x to m, if x < n then f x else 0 :=
begin
  rw sum_fun_restrict' f n (m - n),
  rw nat.add_sub_of_le h,
end

lemma sum_congr (f g : ℕ → ℕ) (n : ℕ) (h : ∀ x < n, f x = g x) :
  ∑ x to n, f x = ∑ x to n, g x :=
begin
  induction n,
  { simp },
  { dunfold sum_fun,
    rw [h, n_ih],
    intros x h', apply h, apply nat.lt.step h',
    apply lt_add_one, },
end

lemma swap_sum (f : ℕ → ℕ → ℕ) (n m : ℕ) : ∑ x to n, ∑ y to m, f x y = ∑ y to m, ∑ x to n, f x y :=
begin
  induction n generalizing m,
  { simp, },
  { dunfold sum_fun,
    rw sum_add_eq_add_sum,
    rw n_ih, }
end

@[simp]
lemma indic_indic_eq_and (a b : Prop) [decidable a] [decidable b]:
  (if a then (if b then 1 else 0) else 0) = (if a ∧ b then 1 else 0) :=
begin
  split_ifs; try { refl <|> { exfalso, cc } },
end

lemma darts_eq_twice_edges (G : graph) : darts G = 2 * edges G :=
begin
  dsimp only [darts, edges],
  have key := λ x (h : x < G.V), sum_fun_restrict (λ y, if G.E x y then 1 else 0) x G.V (by linarith),
  rw sum_congr _ _ _ key, clear key,
  simp,
  rw two_mul,
  conv_rhs { congr, rw swap_sum, },
  rw ←sum_add_eq_add_sum,
  apply sum_congr,
  intros x xel,
  rw ←sum_add_eq_add_sum,
  apply sum_congr,
  intros y yel,
  by_cases h : (G.E x y : Prop),
  simp [h, G.E_symmetric x y xel yel h],
  split_ifs; try { refl <|> cc },
  exfalso, exact nat.lt_asymm h_1 h_2,
  exfalso,
  have h' : x = y := by linarith,
  subst x, exact G.E_irreflexive _ yel h,
  have h' : ¬ G.E y x,
  { revert h, contrapose, push_neg, exact G.E_symmetric y x yel xel },
  simp [h, h'],
end

lemma darts_eq_sum_degrees (G : graph) : darts G = ∑ x to G.V, degree G x := rfl

theorem sum_degrees (G : graph) : ∑ x to G.V, degree G x = 2 * edges G :=
begin
  rw ←darts_eq_sum_degrees,
  rw ←darts_eq_twice_edges,
end
