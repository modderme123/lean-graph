import tactic
import data.nat.basic

structure graph := (V : ℕ)
  (E : ℕ → ℕ → bool)
  (E_irreflexive : forall x : ℕ, x < V → ¬ E x x)
  (E_symmetric : forall x y : ℕ, x < V ∧ y < V → E x y → E y x)

def K (n: ℕ): graph := begin
  refine_struct ({
    V := n, 
    E := (λ x, λ y, x ≠ y),
  }),
  intros,
  intro z,
  simp at z,
  tauto,
  intros x h l,
  simp,
  intro x,
  cc,
end

def Path (n: ℕ): graph := begin
  refine_struct ({
    V := n, 
    E := (λ x, λ y, nat.succ x = y ∨ x = nat.succ y),
  }),
  intros,
  simp,
  intro j,
  have x := nat.succ_ne_self x,
  cc,
  simp,
  intros,
  have x := nat.succ_ne_self x,
  cc,
end

def Empty (n: ℕ): graph := begin
  refine_struct ({
    V := n, 
    E := (λ x, λ y, false),
  }),tauto,tauto,
end

def summer : (nat → nat) -> nat → nat
| m 0 := 0
| m (nat.succ n) := m(n) + summer(m)(n)

def edges (G : graph) : nat := begin
  have sum := fun x, (summer (fun y, if G.E(x)(y) then 1 else 0) x),
  exact summer (sum) (G.V)
end

def degree (G : graph) (x : nat) : nat := begin
  have check_edge := λ y, if G.E x y then 1 else 0,
  exact if x<G.V then summer check_edge (G.V) else 0
end

def x := K(4)
#eval edges(x)
#eval degree(x)(0)

theorem sum_degrees (G : graph) : summer (degree G) (G.V) = 2 * (edges G) :=
begin

  sorry
end