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

def sum_fun : (nat → nat) -> nat → nat
| m 0 := 0
| m (nat.succ n) := m(n) + sum_fun(m)(n)

def edges (G : graph) : nat := begin
  have sum := λ x, (sum_fun (λ y, if G.E x y then 1 else 0) x),
  exact sum_fun (sum) (G.V)
end

def degree (G : graph) (x : nat) : nat := begin
  have check_edge := λ y, if G.E x y then 1 else 0,
  exact if x < G.V then sum_fun check_edge (G.V) else 0
end

theorem sum_degrees (G : graph) : sum_fun (degree G) (G.V) = 2 * (edges G) :=
begin
  sorry
end

def x := K(10)
#eval 2 * edges(x)
#eval sum_fun (degree x) (x.V)
