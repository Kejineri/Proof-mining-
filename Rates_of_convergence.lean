import data.real.basic
import tactic.suggest
import analysis.normed_space.operator_norm
import analysis.normed_space.dual
import data.fin 
import algebra.big_operators.basic
import data.finset.intervals
import tactic.linarith
import tactic.norm_num
open  continuous_linear_map
open finset opposite

open_locale big_operators


noncomputable theory
open_locale classical

notation `|`x`|` := abs x

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

variables {X : Type*} [normed_group X] [normed_space ℝ  X] [complete_space X]

def J (x: X) := {j : normed_space.dual ℝ X | j x = ∥x∥^2 ∧ j x = ∥j∥^2}

lemma geom_ineq (x y : X) (j ∈ J(x+y)) : ∥x + y∥^2 ≤ ∥x∥^2 + 2*(j y):=
begin
  unfold J at H,
  rw set.mem_set_of_eq at H,
  have h1 : j x ≤ ∥j∥* ∥x∥, 
    begin 
      calc (j x: ℝ)  ≤ ∥j x∥ : by exact le_abs_self (j x)
      ... ≤ ∥j∥* ∥x∥ : by {exact le_op_norm j x}
    end,
  have h3: ∥x+y∥^2 = ∥j∥^2,
  cases H,
  calc  ∥x+y∥^2 = j (x+y) : by exact eq.symm H_left
  ...   = ∥j∥^2 : by {exact H_right},
  have h4: ∥x+y∥ = ∥j∥,
  exact (pow_left_inj  (norm_nonneg (x+y)) (norm_nonneg j) (by simp)).1 h3,
 have h5 : ∥x + y∥^2  ≤ ∥x+y∥* ∥x∥ + j y ,
      begin
        calc ∥x + y∥^2 = j(x + y) : by {rw H.1}
        ... = j x + j y : by simp
        ...≤ ∥j∥* ∥x∥ + j y : by exact add_le_add_right h1 (j y)
        ... =   ∥x+y∥* ∥x∥ + j y : by exact congr_arg2 has_add.add (congr_fun (congr_arg has_mul.mul (eq.symm h4)) ∥x∥) rfl
      end,
  have h6 : 0 ≤ (∥x∥ - ∥x+y∥)^2,
  exact sq_nonneg (∥x∥ - ∥x + y∥),
  have h7 : 0 ≤ (∥x∥^2 + ∥x+y∥^2) - ∥x∥*∥x+y∥*(1/2)⁻¹,
  calc 0 ≤ (∥x∥ - ∥x+y∥)^2 : by exact h6
  ... = (∥x∥^2 + ∥x+y∥^2) - ∥x∥*∥x+y∥*(1/2)⁻¹: by ring,
  have h8 : 0 ≤ (∥x∥^2)*(1/2) + (∥x+y∥^2)*(1/2) - ∥x+y∥*∥x∥,
  calc 0 ≤ ((∥x∥^2 + ∥x+y∥^2) - ∥x∥*∥x+y∥*(1/2)⁻¹)*(1/2) : by exact mul_nonneg h7 (by simp)
  ... = (∥x∥^2)*(1/2) + (∥x+y∥^2)*(1/2) - ∥x+y∥*∥x∥: by ring,
  have h9 : ∥x+y∥*∥x∥ ≤ (∥x∥^2)*(1/2) + (∥x+y∥^2)*(1/2),
  exact sub_nonneg.mp h8,
  have h10 : ∥x + y∥^2 ≤ (∥x∥^2)*(1/2) + (∥x+y∥^2)*(1/2) + j y,
  exact le_add_of_le_add_right h5 h9,
  have h11: 0 ≤ (∥x∥^2)*(1/2) + (∥x+y∥^2)*(1/2) + j y - ∥x + y∥^2,
  exact sub_nonneg.mpr h10,
  have h12 : 0 ≤ (∥x∥^2)*(1/2) + j y - (∥x+y∥^2)*(1/2),
  calc  0 ≤ (∥x∥^2)*(1/2) + (∥x+y∥^2)*(1/2) + j y - ∥x + y∥^2 : by exact h11
  ... = (∥x∥^2)*(1/2) + j y - (∥x+y∥^2)*(1/2) : by ring,
  have h13 : 0 ≤ (∥x∥^2) + 2*j y - ∥x+y∥^2,
  calc  0 ≤ ((∥x∥^2)*(1/2) + j y - (∥x+y∥^2)*(1/2))*2 : by exact mul_nonneg h12 (by simp)
  ... = (∥x∥^2) + 2*j y - ∥x+y∥^2 : by ring,
  exact sub_nonneg.mp h13,

end


def Dom (A: X → set X ) := {x : X | A x ≠ ∅ }

def Range (A: X → set X) := {y : X | ∃ x : X, y ∈ A x}

def accretive (A: X → set X) :=∀ x y (u :A x) (v : A y), (∃ j : J(x-y), j(u-v) ≥ 0)

def strong_accretive (ψ: nnreal  → nnreal ) (A: X → set X):= (continuous ψ) ∧ ∀ x y (u :A x) (v : A y),(∃ j : J(x-y), j(u-v) ≥ ψ(real.to_nnreal ∥x-y∥)*∥x - y∥) 

def nnseq:= {u : ℕ → ℝ // ∀ (n : ℕ), u n ≥ 0}

def zero_limit := {α : nnseq | seq_limit α.1  0}

def div_sum := {α : nnseq | ¬ summable α.1 }

def RoC (φ: {x: ℝ // x > 0} → ℕ ) (α : nnseq) := ∀ ε : {x: ℝ // x > 0}, ∀ n ≥ φ ε , α.1 n ≤ ε   

def RoD (r: ℕ → {x: ℝ // x > 0} → ℕ )(α : nnseq) :=  ∀N:ℕ, ∀x:{x: ℝ // x > 0} ,N ≤ r N x ∧ ∀(N : ℕ),∀ (x : {x: ℝ // x > 0}),(∑ i in (finset.Ico N ((r N x) + 1)), α.1 i) > x


lemma sum_le {T : Type*} (s : finset T) (f g : T → ℝ ) :
(∀ i ∈ s, f i ≤ g i) →  (∑ i in s, f i) ≤ ∑ i in s, (g i)
 :=
begin
  classical,
  apply finset.induction_on s,
  simp only [finset.sum_empty], simp,
  intros i s his IH,
    simp only [his, finset.sum_insert, not_false_iff],
    intro h,
    have h1:  ∀(i : T), i ∈ s → f i ≤ g i,
    intros l hl, specialize h l, exact h (mem_insert_of_mem hl) ,
    have h2: s.sum f ≤ s.sum g, exact IH h1,specialize h i,simp at h,
    exact add_le_add h (IH h1),
end
lemma sum_dist {T : Type*} {s : finset T}{f : T → ℝ}{k : ℝ} :
 ∑ i in s, ((f i)*k) = (∑ i in s, (f i))*k:= sorry 


lemma abstract_lemma1 (θ : nnseq )(α : nnseq)(K: {x: ℝ // x > 0}) (r: ℕ → {x: ℝ // x > 0} → ℕ ) 
(N : {x:ℝ // x > 0 }  → ℕ ) (φ : {x:ℝ // x > 0 }  → {x:ℝ // x > 0 }) 
(h1 : ∀(n:ℕ), (θ.1 n) < K) (h2: RoD r α) 
(h3: ∀ ε : {x:ℝ // x > 0 } , ∀ n ≥ N(ε), (ε:ℝ) < θ.1 (n + 1)  → θ.1 (n + 1) ≤ θ.1 n - (α.1 n)*φ(ε)): 
RoC (λ ε : {x: ℝ // x > 0},  r (N ε) ⟨K/(φ ε), div_pos K.2 (φ ε).2 ⟩ + 1) θ  := 
begin
have 
H1 : ∀ ε : {x:ℝ // x > 0 },∀ n ≥ N(ε), θ.1 n ≤ ε  → θ.1 (n + 1) ≤ ε,
by_contradiction p1,
push_neg at p1,
cases p1 with ε p2,
cases p2 with n p3,
have p5 : ε < ε,
calc ε.1 < θ.1 (n+1): (p3.2).2   
... ≤ θ.1 n - (α.1 n)*φ(ε): h3 ε n p3.1 (p3.2).2
... ≤ θ.1 n : sub_le_self (θ.1 n) (mul_nonneg (α.2 n) (le_of_lt (φ ε).2 ))
... ≤ ε :(p3.2).1,
exact (lt_self_iff_false ε).mp p5,
have H2 : ∀ ε : {x :ℝ // x > 0}, ∃ n ∈ finset.Ico (N ε) ((r (N ε) ⟨↑K / ↑(φ ε), _⟩) + 1), θ.1 (n + 1) ≤ ε,
by_contradiction,
push_neg at h,
cases h with ε h,
have H3: ∀ (n : ℕ), n ∈ finset.Ico (N ε) ((r (N ε) ⟨↑K / ↑(φ ε), _⟩) + 1) → θ.1 (n + 1) ≤ θ.1 n - (α.1 n)*φ(ε),
intros n h_n, 
--imp at h_n,
--simp at h,
have h_n1 : N ε ≤ n ,rw mem_Ico at h_n, exact h_n.1, exact div_pos K.2 (φ ε).2,
rw ← ge_iff_le at h_n1, exact h3 ε n h_n1(h n h_n), 
have H3':  ∀ (n : ℕ), n ∈ finset.Ico (N ε) ((r (N ε) ⟨↑K / ↑(φ ε), _⟩) + 1) → (α.1 n)*φ(ε) ≤ θ.1 n - θ.1 (n + 1),
intros n hn, specialize H3 n hn, rw le_sub, exact H3,
have sum: (∑ i in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1),(λ i, α.val i * ↑(φ ε))i) ≤ 
(∑ i in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1),(λ i,θ.val i - θ.val (i + 1))i),
apply sum_le, exact H3',
have split: (∑ i in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1),(λ i,θ.val i - θ.val (i + 1))i) =
(∑ i in range (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1),(λ i,θ.val i - θ.val (i + 1))i) - 
(∑ i in range (N ε),(λ i,θ.val i - θ.val (i + 1))i),
rw sum_Ico_eq_sub,
calc N ε ≤ r (N ε) ⟨↑K / ↑(φ ε), _⟩: (h2 (N ε)  ⟨↑K / ↑(φ ε), _⟩).1
... ≤  r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1: nat.le_succ (r (N ε) ⟨↑K / ↑(φ ε), div_pos K.2 (φ ε).2⟩),
rw split at sum, 
rw sum_range_sub' at sum, rw sum_range_sub' at sum, simp at sum,
have p: ∑ (x : ℕ) in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1), α.1 x * ↑(φ ε)< K,
calc ∑ (x : ℕ) in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1), α.1 x * ↑(φ ε) ≤ θ.1 (N ε) - θ.1 (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1): sum
... ≤ θ.1 (N ε): sorry
... < K : h1 (N ε),
have q : (∑ (x : ℕ) in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1), α.val x) * ((φ ε).1)* ((φ ε).1)⁻¹ ≤  ↑K* ((φ ε).1)⁻¹,
simp[ le_of_lt] at p, rw sum_dist at p,
exact mul_le_mul_of_nonneg_right (le_of_lt p)(le_of_lt ((@inv_pos ℝ _ (φ ε).1).2((φ ε).2))) ,
have inv : (φ ε).val * ((φ ε).val)⁻¹ =1,
exact mul_inv_cancel (norm_num.ne_zero_of_pos (φ ε).1 (φ ε).2),
rw mul_assoc at q, rw inv at q,simp at q,
--rw ←  one_div at q,


--rw ←  one_div at q, rw (@mul_mul_inv_of_self_cancel ℝ _  (∑ (x : ℕ) in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1), α.val x) (φ ε).1)(invertible_of_nonzero (norm_num.ne_zero_of_pos (φ ε).1 (φ ε).2)) at q,
--exact norm_num.ne_zero_of_pos
--rw mul_assoc at q, rw mul_inv_self  at q,
--exact mul_inv_cancel
exact 









/-
unfold RoC,
intros, 
have p6 : n>0,
calc n ≥ r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1 : by exact H
... ≥ 0 + 1: by exact le_add_self
... > 0: by simp,
let k := (n-1: ℕ ),
have p7 : k + 1 = n,
calc k + 1 = n - 1 + 1 : by refl
... = n.pred.succ  : by refl
... = n : by rw nat.succ_pred_eq_of_pos p6,
have p8:  n-1 ≥ r (N ε) ⟨↑K / ↑(φ ε), _⟩,
by_contradiction,
push_neg at h,
have h'  : n  < r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1,
calc n = n.pred.succ : by rw nat.succ_pred_eq_of_pos p6
... = n - 1 + 1 : by refl
... < r (N ε) ⟨↑K / ↑(φ ε),by exact div_pos K.2 (φ ε).2 ⟩ + 1 : by exact add_lt_add_right h 1,
have p9: ¬ (n  ≥  r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1),
push_neg,
exact h',
contradiction,
have p10: k ≥ r (N ε) ⟨↑K / ↑(φ ε), _⟩,
calc k = n-1 : by refl
... ≥ r (N ε) ⟨↑K / ↑(φ ε), _⟩ : by exact p8,
rw eq_comm at p7,
rw p7,
by_contradiction,
push_neg at h,
-/













end


