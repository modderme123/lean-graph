import tactic

structure graph := (V : ℕ)
  (E : ℕ → ℕ → bool)
  (E_irreflexive : forall x : ℕ, x < V → ¬ E x x)
  (E_symmetric : forall x y : ℕ, x < V ∧ y < V → E x y → E y x)

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

def edges (G : graph) : ℕ :=
let sum := λ x, sum_fun (λ y, if G.E x y then 1 else 0) x
in sum_fun sum G.V

def degree (G : graph) (x : ℕ) : ℕ :=
let check_edge := λ y, if G.E x y then 1 else 0
in sum_fun check_edge G.V

def darts (G : graph) : ℕ :=
let sum := λ x, sum_fun (λ y, if G.E x y then 1 else 0) G.V
in sum_fun sum G.V

lemma darts_eq_twice_edges (G : graph) : darts G = 2 * edges G :=
begin
  dsimp only [darts, edges],
  sorry,
end

lemma darts_eq_sum_degrees (G : graph) : darts G = sum_fun (degree G) G.V :=
begin
  sorry
end

theorem sum_degrees (G : graph) : sum_fun (degree G) G.V = 2 * edges G :=
begin
  rw ←darts_eq_sum_degrees,
  rw ←darts_eq_twice_edges,
end

def x := K(10)
#eval 2 * edges(x)
#eval sum_fun (degree x) (x.V)
