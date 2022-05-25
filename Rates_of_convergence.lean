import data.real.basic
import analysis.normed_space.operator_norm
import analysis.normed_space.dual
import data.fin 
import algebra.big_operators.basic
import data.finset.intervals


open  continuous_linear_map
open finset opposite

open_locale big_operators


--noncomputable theory
--open_locale classical

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

def RoD (r: ℕ → {x: ℝ // x > 0} → ℕ )(α : nnseq) :=  (∀N:ℕ, ∀x:{x: ℝ // x > 0} ,N ≤ r N x) ∧ ∀(N : ℕ),∀ (x : {x: ℝ // x > 0}),(∑ i in (finset.Ico N ((r N x) + 1)), α.1 i) > x.1


lemma abstract_lemma1 (θ : nnseq )(α : nnseq)(K: {x: ℝ // x > 0}) (r: ℕ → {x: ℝ // x > 0} → ℕ ) 
(N : {x:ℝ // x > 0 }  → ℕ ) (φ : {x:ℝ // x > 0 }  → {x:ℝ // x > 0 }) 
(h1 : ∀(n:ℕ), (θ.1 n) < K) (h2: RoD r α) 
(h3: ∀ ε : {x:ℝ // x > 0 } , ∀ n ≥ N(ε), (ε:ℝ) < θ.1 (n + 1)  → θ.1 (n + 1) ≤ θ.1 n - (α.1 n)*φ(ε)): 
RoC (λ ε : {x: ℝ // x > 0},  (r (N ε) ⟨K/(φ ε), div_pos K.2 (φ ε).2 ⟩+1)) θ  := 
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
have H2 : ∀ ε : {x :ℝ // x > 0}, ∃ n ∈ finset.Ico (N ε) ((r (N ε) ⟨↑K / ↑(φ ε), _⟩)+1), θ.1 (n + 1) ≤ ε,
by_contradiction,
push_neg at h,
cases h with ε h,
have H3: ∀ (n : ℕ), n ∈ finset.Ico (N ε) ((r (N ε) ⟨↑K / ↑(φ ε), _⟩) +1) → θ.1 (n + 1) ≤ θ.1 n - (α.1 n)*φ(ε),
intros n h_n, 
have h_n1 : N ε ≤ n ,rw mem_Ico at h_n, exact h_n.1, exact div_pos K.2 (φ ε).2,
rw ← ge_iff_le at h_n1, exact h3 ε n h_n1(h n h_n), 
have H3':  ∀ (n : ℕ), n ∈ finset.Ico (N ε) ((r (N ε) ⟨↑K / ↑(φ ε), _⟩)+1) → (α.1 n)*φ(ε) ≤ θ.1 n - θ.1 (n + 1),
intros n hn, specialize H3 n hn, rw le_sub, exact H3,
have sum: (∑ i in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1),(λ i, α.val i * ↑(φ ε))i) ≤ 
(∑ i in Ico (N ε) ((r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1)),(λ i,θ.val i - θ.val (i + 1))i),
apply sum_le_sum, exact H3',
have split: (∑ i in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1),(λ i,θ.val i - θ.val (i + 1))i) =
(∑ i in range (r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1),(λ i,θ.val i - θ.val (i + 1))i) - 
(∑ i in range (N ε),(λ i,θ.val i - θ.val (i + 1))i),
rw sum_Ico_eq_sub,
have l: N ε ≤ r (N ε) ⟨↑K / ↑(φ ε), _⟩, 
exact (h2.1 (N ε)  (⟨↑K / ↑(φ ε), div_pos K.2 (φ ε).2⟩ )),exact le_add_right l,
rw split at sum, 
rw sum_range_sub' at sum, rw sum_range_sub' at sum, simp at sum,
have p: ∑ (x : ℕ) in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ + 1), α.1 x * ↑(φ ε)< K,
have w: θ.1 (r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1) ≥ 0, exact θ.2 (r (N ε) ⟨↑K / ↑(φ ε) , div_pos K.2 (φ ε).2⟩+1 ),
calc ∑ (x : ℕ) in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1), α.1 x * ↑(φ ε) ≤ θ.1 (N ε) - θ.1 (r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1): sum
... ≤ θ.1 (N ε): by linarith
... < K : h1 (N ε),
have q : (∑ (x : ℕ) in Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩+1), α.val x) * ((φ ε).1)* ((φ ε).1)⁻¹ ≤  ↑K* ((φ ε).1)⁻¹,
simp[ le_of_lt] at p, rw ← sum_mul at p,
exact mul_le_mul_of_nonneg_right (le_of_lt p)(le_of_lt ((@inv_pos ℝ _ (φ ε).1).2((φ ε).2))) ,
have inv : (φ ε).val * ((φ ε).val)⁻¹ =1,
exact mul_inv_cancel (norm_num.ne_zero_of_pos (φ ε).1 (φ ε).2),
rw mul_assoc at q, rw inv at q,simp at q, 
have cont: (Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1)).sum α.1 > ↑K * (↑(φ ε))⁻¹,
calc  (Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1)).sum α.1 >  K.1 / (φ ε).1 : (h2.2 (N ε) ⟨↑K / ↑(φ ε), _⟩)
... =  ↑K * (↑(φ ε))⁻¹ : rfl, exact div_pos K.2 (φ ε).2,
have cont': ¬  ((Ico (N ε) (r (N ε) ⟨↑K / ↑(φ ε), _⟩ +1)).sum α.1 ≤ ↑K * (↑(φ ε))⁻¹),
push_neg, rw ← gt_iff_lt, exact cont, contradiction,
unfold RoC, intros,
specialize H2 ε,cases H2 with R, cases H2_h with H2_N,
have induct:  ∀k :ℕ, k> R → θ.1 k ≤ ε,
intros, induction k,
have Nnonneg: ¬ (0> R),push_neg,simp, contradiction,
have S1: k_n ≥ R, exact nat.lt_succ_iff.mp ᾰ,
rw ge_iff_le at S1, rw le_iff_lt_or_eq at S1, cases S1, rw ← gt_iff_lt at S1,
rw mem_Ico at H2_N,
have S2: k_n ≥ N ε, linarith,
exact H1 ε k_n S2 (k_ih S1),
rw S1 at H2_h_h, exact H2_h_h,
rw mem_Ico at H2_N,
have S3 : n > R, linarith, exact induct n S3, 
end


