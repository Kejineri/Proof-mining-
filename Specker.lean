
import data.real.basic
import data.real.cau_seq
import computability.halting
import computability.partrec_code
import computability.primrec
import data.nat.gcd
import data.int.cast
import data.equiv.encodable.basic
open_locale classical

def nnseqR := {u : ℕ → ℝ // ∀ (n : ℕ), u n ≥ 0}
def nnseqQ := {u : ℕ → ℚ // ∀ (n : ℕ), u n ≥ 0}

def RoC (φ: ℕ  → ℕ ) (α : nnseqR) := ∀ k > (0 : ℕ ), ∀ n m ≥ φ k , abs((α.1 m) - (α.1 n)) < (1/k) 


def temp: ∀ ε>(0:ℝ), ∃ k > (0: ℕ ) , (1/k :ℝ) < ε:=
begin
intros,
use  nat.ceil(1 / ε) + 1,
have h₁: (1/ε)< nat.ceil(1 / ε) + 1,
  calc (1/ε) ≤ nat.ceil(1 / ε): by exact nat.le_ceil (1/ε)
  ... < nat.ceil(1 / ε) + 1: by exact lt_add_one (nat.ceil(1 / ε)),
have h₂ : 0 < (nat.ceil(1 / ε):ℝ ) + 1,
  calc 0 < (1/ε) :by exact one_div_pos.mpr H
  ... < nat.ceil(1 / ε) + 1 : by exact h₁,
simp at h₁,
split,
norm_num,
simp,
exact inv_lt_of_inv_lt H h₁,
end
def tempQ: ∀ ε>(0:ℚ), ∃ k > (0: ℕ ) , (1/k :ℚ) < ε:=
begin
intros,
use  nat.ceil(1 / ε) + 1,
have h₁: (1/ε) < (nat.ceil(1 / ε):ℚ) + 1,
  calc (1/ε) ≤ nat.ceil(1 / ε): by exact nat.le_ceil (1/ε)
  ... < nat.ceil(1 / ε) + 1: by exact lt_add_one (nat.ceil(1 / ε)),
have h₂ : 0 < (nat.ceil(1 / ε):ℚ)  + 1,
  calc 0 < (1/ε) :by exact one_div_pos.mpr H
  ... < nat.ceil(1 / ε) + 1 : by exact h₁,
simp at h₁,
split,
norm_num,
simp,
exact inv_lt_of_inv_lt H h₁,
end

def RoM (φ: ℕ → (ℕ → ℕ) → ℕ )(α : nnseqR) := ∀ k > (0 : ℕ), ∀ (g: ℕ → ℕ), ∃ n <φ k g, ∀ i ∈  {i :ℕ  | i ≥  n ∧ i ≤  (n  + (g n))}, ∀ j ∈  {i :ℕ  | i ≥  n ∧ i ≤  (n  + (g n))} , abs((α.1 i) - (α.1 j)) < (1/k)

theorem RoC_implies_cauchy {α : nnseqR} (h: ∃ (φ: ℕ → ℕ ), RoC φ α) : (is_cau_seq abs α.1) := 
begin
intros ε h₁,
cases h with φ h₂,
have h₄ :∃ k > (0 : ℕ) , (1/k :ℝ) < ε,
exact temp ε h₁,
cases h₄ with k h₅,
cases h₅ with h₆ h₇,
use φ k,
specialize h₂ k h₆ (φ k),
intros j h₃,
have h₈ : |α.val j - α.val (φ k)| < (1/k),
exact h₂ j (by norm_num) h₃,
calc |α.val j - α.val (φ k)| < (1/k) : by exact h₈
... < ε : by exact h₇,
end

theorem RoM_implies_cauchy {α : nnseqR} (h: ∃ (φ: ℕ  → (ℕ → ℕ) → ℕ ), RoM φ α) : (is_cau_seq abs α.1) :=
begin
intros ε h₁,
cases h with φ h₂,
intros,
by_contradiction h₃,
push_neg at h₃,
cases classical.axiom_of_choice h₃ with f h₄,
let g : ℕ → ℕ  := λ x, f x - x,
have h₅ :∃ k > (0 : ℕ) , (1/k :ℝ) < ε,
exact temp ε h₁,
cases h₅ with k h₆,
cases h₆ with h₇ q,
specialize h₂ k h₇ g,
cases h₂ with n h₅,
cases h₅ with h₆ h₇,
have h₈ : n ∈  {i :ℕ  | i ≥  n ∧ i ≤  (n  + (g n))},
simp,
have h₉ : f n ∈  {i :ℕ  | i ≥  n ∧ i ≤  (n  + (g n))},
simp,
split,
exact (h₄ n).1,
rw ←  nat.add_sub_assoc (h₄ n).1,
rw add_comm n (f n),
rw nat.add_sub_assoc,
simp,
specialize h₇ n h₈ (f n) h₉,
specialize h₄ n,
rw abs_sub_comm at h₇,
have p : ¬ |α.val (f n) - α.val n| < ε,
push_neg,
exact h₄.2,
have p :|α.val (f n) - α.val n| < ε,
calc |α.val (f n) - α.val n| < 1 / ↑k : by exact h₇
... < ε : by exact q,
contradiction,
end

open computable part nat.partrec (code) nat.partrec.code

def  s_prop(n :ℕ ) : ℕ → Prop:= (λ (m : ℕ),
       m ≤ n ∧
         (∃ (x : ℕ), evaln n (of_nat_code m) 0 = some x) ∧
           ∀ (l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code m) 0 = some w)

@[instance] def s_decideable (n :ℕ) :decidable_pred (s_prop n) :=
begin
unfold decidable_pred,
intros,
have h₁: decidable (a ≤ n),
exact nat.decidable_le a n,
have h₂ : ∀ o : option ℕ, decidable( ∃ x, o = some x),
--exact option.decidable_forall_mem,
intros,
apply option.rec_on o, simp, 
exact decidable.false, intros, simp, exact decidable.true,
specialize h₂ (evaln n (of_nat_code a) 0),
have h₃ : decidable(∀ (l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code a) 0 = some w),
let P : fin n → Prop := λ l, ∀ (w : ℕ), ¬evaln l (of_nat_code a) 0 = some w,
have h₄ : decidable_pred P,
unfold decidable_pred,
intros l,
simp[P],
have h₅ : ∀ o : option ℕ, decidable( ∀ (w : ℕ), ¬ o =some w),
intros,
apply option.rec_on o, simp, exact decidable.true, intros, simp,
have p₁: ¬ ∀ (w : ℕ), ¬val = w,
push_neg, use val, exact is_false p₁,
exact h₅ (evaln l (of_nat_code a) 0),
have h₆ : decidable(∀ l : fin n, P l),
exact @nat.decidable_forall_fin n P h₄,
simp[P] at h₆,
dsimp[ fin] at h₆,
have h₇: ∀ Q : ℕ → Prop, (∀ l : fin n, Q l) ↔ (∀ l < n, Q l),
intros,split,intros Q₁ l Q₂, exact Q₁ ⟨ l, Q₂⟩, intros Q₁ l, exact Q₁ l.1 l.2,
specialize h₇ (λl, ∀ (w : ℕ), ¬evaln l (of_nat_code a) 0 = some w), simp at h₇,
exact  decidable_of_decidable_of_iff h₆ h₇,
have h₈ : decidable ((∃ x, (evaln n (of_nat_code a) 0) = some x) ∧  (∀ l < n,  ∀ w, ¬ (evaln l (of_nat_code a) 0) = some w)),
exact @and.decidable (∃ x, (evaln n (of_nat_code a) 0) = some x)  (∀ l < n,  ∀ w, ¬ (evaln l (of_nat_code a) 0) = some w) h₂ h₃,
exact @and.decidable (a ≤ n) ((∃ x, (evaln n (of_nat_code a) 0) = some x) ∧ ∀ l < n,  ∀ w, ¬ (evaln l (of_nat_code a) 0) = some w) h₁ h₈,

end

@[instance] def s_exist_decidable (n : ℕ ): decidable (∃ (m : ℕ), s_prop n m):= 
begin
unfold s_prop,
let P : ℕ → Prop:= λ m, (∃ (x : ℕ), evaln n (of_nat_code m) 0 = some x) ∧ ∀ (l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code m) 0 = some w,
have h₁ : decidable_pred P,
unfold decidable_pred,
intros,
simp[P],
have h₂ : ∀ o : option ℕ, decidable( ∃ x, o = some x),
intros,
apply option.rec_on o, simp, 
exact decidable.false, intros, simp, exact decidable.true,
specialize h₂ (evaln n (of_nat_code a) 0),
have h₃ : decidable(∀ (l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code a) 0 = some w),
let P : fin n → Prop := λ l, ∀ (w : ℕ), ¬evaln l (of_nat_code a) 0 = some w,
have h₄ : decidable_pred P,
unfold decidable_pred,
intros l,
simp[P],
have h₅ : ∀ o : option ℕ, decidable( ∀ (w : ℕ), ¬ o =some w),
intros,
apply option.rec_on o, simp, exact decidable.true, intros, simp,
have p₁: ¬ ∀ (w : ℕ), ¬val = w,
push_neg, use val, exact is_false p₁,
exact h₅ (evaln l (of_nat_code a) 0),
have h₆ : decidable(∀ l : fin n, P l),
exact @nat.decidable_forall_fin n P h₄,
simp[P] at h₆,
dsimp[ fin] at h₆,
have h₇: ∀ Q : ℕ → Prop, (∀ l : fin n, Q l) ↔ (∀ l < n, Q l),
intros,split,intros Q₁ l Q₂, exact Q₁ ⟨ l, Q₂⟩, intros Q₁ l, exact Q₁ l.1 l.2,
specialize h₇ (λl, ∀ (w : ℕ), ¬evaln l (of_nat_code a) 0 = some w), simp at h₇,
exact  decidable_of_decidable_of_iff h₆ h₇,
have h₈ : decidable ((∃ x, (evaln n (of_nat_code a) 0) = some x) ∧  (∀ l < n,  ∀ w, ¬ (evaln l (of_nat_code a) 0) = some w)),
exact @and.decidable (∃ x, (evaln n (of_nat_code a) 0) = some x)  (∀ l < n,  ∀ w, ¬ (evaln l (of_nat_code a) 0) = some w) h₂ h₃,
exact h₈,
have h₂ : decidable_pred(λx, ∃ (m : ℕ), m < x ∧ P m ),
exact @nat.decidable_exists_lt P h₁,
simp[decidable_pred] at h₂, specialize h₂ (n+1), simp[P] at h₂,
have h₃ : (∃ m , m < (n + 1) ∧ (∃ (x : ℕ), evaln n (of_nat_code m) 0 = some x) ∧ 
∀ (l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code m) 0 = some w) ↔ 
(∃ (m : ℕ), m ≤ n  ∧ (∃ (x : ℕ), evaln n (of_nat_code m) 0 = some x) ∧ 
∀ (l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code m) 0 = some w),
split, intro H, cases H with m H, use m, split, rw ← nat.lt_add_one_iff, exact H.1, exact H.2,
intro H, cases H with m H, use m, split, rw  nat.lt_add_one_iff, exact H.1, exact H.2,
exact  decidable_of_decidable_of_iff h₂ h₃,
end
def Specker_seq (α: nnseqR):= ∀ φ: ℕ → ℕ, (RoC φ α) → ¬ computable(φ)
@[reducible]
def s (α: nnseqQ): ℕ → ℚ := 
λ n, if h: ∃ m : ℕ, s_prop n m then α.1 (nat.find h) else 0

theorem s_converges (α: nnseqQ)(h₁ : ∀ n m, n < m → α.1 n > α.1 m)(h₂: ∀ ε > (0 :ℝ), ∃ N : ℕ, ∀n≥N, (α.1 n: ℝ) < ε ): ∀ ε > (0 :ℝ), ∃ N : ℕ, ∀n≥N, (s α n : ℝ) < ε := 
begin
intros,
specialize h₂ ε H ,
cases h₂  with N h₃,
by_cases ∃ i < N, ∃ x,  x ∈ (eval (of_nat_code i) 0),
cases h with i h₄, cases h₄ with  h₄ h₅,
let S := {j ∈ finset.range N | ∃ x, x ∈ (eval ( of_nat_code j) 0)},
have p₁: finset.nonempty S,
unfold finset.nonempty,use i,simp[S],split,exact h₄,exact h₅,
let f : ℕ → ℕ := λj, if r : ∃ k: ℕ,  ∃ x, x ∈ (evaln k (of_nat_code j) 0) then (nat.find r) else 0,let S₁ := S.image f,
have p₂: finset.nonempty S₁,
simp,exact p₁,
have p₃ : ∃ x, x ∈ S₁.max,
exact finset.max_of_nonempty p₂,
cases p₃ with k k_h,
use k + 1,
intros,
unfold s,
split_ifs,
swap, simp,
exact H,
let z := nat.find h,
have p₄ : N ≤ z,
by_contradiction q,
push_neg at q,
have p₅ : z ∈ S,
simp[S],
split,
use z,
split,
exact q,
exact nat.find_spec h,
have h' : z ≤ n ∧  (∃ (x : ℕ), evaln n (of_nat_code z) 0 = some x) ∧ ∀ (l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code z) 0 = some w, 
exact nat.find_spec h, 
cases h' with bounded h',
cases h' with h'₁ h'₂,
cases h'₁ with x h'₁,
use x,
have h''₁ : ∃ k, x ∈ evaln k (of_nat_code z) 0,
use n,
exact h'₁,
rw evaln_complete,
exact h''₁,
have p₆ : f z ∈ S₁,
simp[S₁],
use z,
split,
exact p₅, simp,
have p₇: f z ≤ k,
exact finset.le_max_of_mem p₆ k_h,
have p₈ : n ≤ f z,
by_contradiction q₁,
push_neg at q₁,
have h' : z ≤ n ∧ (∃ (x : ℕ), evaln n (of_nat_code z) 0 = some x) ∧ ∀ (l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code z) 0 = some w, 
exact nat.find_spec h, 
cases h' with bounded h',
have h'₁ :  ∀(l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code z) 0 = some w,
exact h'.2,
specialize h'₁ (f z),
have q₂ :∃ (w : ℕ), evaln (f z) (of_nat_code z) 0 = some w,
simp[f],
split_ifs,
have h_1': ∃ (a_2 : ℕ), evaln (nat.find h_1) (of_nat_code z) 0 = some a_2,
exact nat.find_spec h_1,
exact h_1',
have h_1_contra : ∃ (a a_1 : ℕ), evaln a (of_nat_code z) 0 = some a_1,
use n, exact h'.1,
contradiction,
have h'₁_contra : ¬ ∃ (w : ℕ), evaln (f z) (of_nat_code z) 0 = some w,
push_neg,
exact h'₁ q₁, 
contradiction,
have q₃ : k + 1 ≤ k,
calc k + 1 ≤ n : by exact H_1
... ≤ f z : by exact p₈
... ≤ k : by exact p₇,
have q₃' : ¬  k + 1 ≤ k,
push_neg,
exact lt_add_one k,
contradiction,
exact h₃ z p₄,
push_neg at h,
use 0,
intros,
unfold s,
split_ifs, 
swap,simp, exact H,
let z := nat.find h_1,
have h_1' :  z ≤ n ∧ (∃ (x : ℕ), evaln n (of_nat_code z) 0 = some x) ∧ ∀ (l : ℕ), l < n → ∀ (w : ℕ), ¬evaln l (of_nat_code z) 0 = some w,
exact nat.find_spec h_1,
have q : ¬ z < N,
by_contradiction q,
specialize h z,
have q₁ :∀ (x : ℕ), ¬  x ∈ eval (of_nat_code z) 0 ,
exact h q,
have q₂ : ∃ (x : ℕ), evaln n (of_nat_code z) 0 = some x,
exact h_1'.2.1,
cases q₂ with x q₂,
specialize q₁ x,
have q₃ : x ∈ evaln n (of_nat_code z) 0,
simp,
exact q₂,
have q₃': ∃ k, x ∈ evaln k (of_nat_code z) 0,
use n, exact q₃,
rw ← evaln_complete at q₃',
contradiction,
push_neg at q,
exact h₃ z q,

end

theorem bound (n: ℕ) {P : ℕ → Prop} [decidable_pred P] (hP: primrec_pred P): 
primrec_pred(λ x :ℕ , ∀ x ≤ n, P x):=
begin
unfold primrec_pred,

end

 --def coprime_prim: ∀ n : ℕ , primrec_pred(λ d, n.coprime d):= 

instance : primcodable ℚ := primcodable.of_equiv (Σ n : ℤ, {d : ℕ // 0 < d ∧ n.nat_abs.coprime d})
  ⟨λ ⟨a, b, c, d⟩, ⟨a, b, c, d⟩, λ⟨a, b, c, d⟩, ⟨a, b, c, d⟩,
   λ ⟨a, b, c, d⟩, rfl, λ⟨a, b, c, d⟩, rfl⟩

instance PrimcodeQ : primcodable ℚ:= sorry

theorem s_specker (α: nnseqQ)(h₀: computable α.1)(h₁ : ∀ n m, n < m → α.1 n > α.1 m)(h₂: ∀ ε > (0 :ℝ), ∃ N : ℕ, ∀n≥N, (α.1 n :ℝ) < ε ):
 ∀ φ: ℚ → ℕ, (∀ ε  > (0 : ℚ), ∀ n > φ ε , ((s α) n) < ε ) → ¬ computable(φ) :=
 begin
 intros φ h₃,
 by_contradiction, 
 have h₄ : ∀ n, α.1 n > 0,
intros,
by_contradiction p,
push_neg at p,
have p₁: α.1 (n + 1) < 0,
calc α.1 (n + 1) < α.1 n : by exact h₁ n (n+1) (lt_add_one n)
...  ≤ 0 : by exact p,
have p₂ : ¬ α.1 (n + 1) < 0,
push_neg,
exact (α.2(n +1)),
contradiction,
--have h₅: ∀ n, ∃ k > (0: ℕ ) , (1/k :ℚ) < α.1 n,
--intro, exact tempQ (α.1 n) (h₄ n),
--let r := λn, nat.find (h₅ n),
let max_halt: ℕ → ℕ  := λ n, max_default n (φ (α.1 (n + 1))),
have h₆ : ∀ n, (∃ x, x ∈ evaln (max_halt n) (of_nat_code n) 0) ↔ (∃ x, x ∈ eval (of_nat_code n) 0), 
intros n, split,swap, intro p₁,
cases p₁ with x,
have p₂ : ∃ k, x ∈ evaln k (of_nat_code n) 0,
rw ←  evaln_complete, exact p₁_h,
have p₂': ∃ k, ∃ x, x ∈ evaln k (of_nat_code n) 0,
cases p₂ with k, use k, use x, exact p₂_h,
let k:= nat.find p₂',
have p₃ : k ≤ max_halt n,
by_contradiction p₃, push_neg at p₃,
have p₄: n ≤ max_halt n,
simp[max_halt], unfold max_default, split_ifs, simp, simp at h_1, exact le_of_lt h_1,
have p₅: n < k,
calc n ≤ max_halt n : by exact p₄
... < k: by exact p₃,
have p₆:s_prop k n,
unfold s_prop,split,exact le_of_lt p₅,split, exact nat.find_spec p₂',
intro,
have min: l < k → ¬∃(w : ℕ),evaln l (of_nat_code n) 0 = some w,
exact nat.find_min p₂',push_neg at min, exact min,
have p₇: s α k ≥ α.1 n,
unfold s, split_ifs,
have p₈: nat.find h_1 ≤ n, exact nat.find_min' h_1 p₆,
have p₈': nat.find h_1 < n ∨ nat.find h_1 = n,
exact lt_or_eq_of_le p₈, cases p₈',
exact le_of_lt (h₁ (nat.find h_1) n p₈'), exact (congr_arg α.val p₈').ge,
push_neg at h_1,specialize h_1 n, contradiction,
have p₈ : α.val n > α.val (n + 1),
exact h₁ n (n+1) (lt_add_one n),
have p₉ : s α k > α.val (n + 1),
calc s α k ≥ α.1 n : by exact p₇
... > α.val (n + 1) : by exact p₈,
have q₁ : φ (α.1 (n + 1)) ≤ max_halt n,
simp[max_halt], unfold max_default, split_ifs, exact  h_1, simp,
have q₂:  φ (α.1 (n + 1)) < k,
calc φ (α.1 (n + 1)) ≤ max_halt n : by exact q₁
...< k : by exact p₃,
rw ← gt_iff_lt at q₂,
have h₉': s α k < α.val (n + 1),
exact h₃ (α.1 (n+1)) (h₄ (n + 1)) k q₂,
have h₉'': ¬ s α k < α.val (n + 1),
push_neg, exact le_of_lt p₉, contradiction,
have spec: ∃ x, x ∈ evaln k (of_nat_code n) 0,
exact nat.find_spec p₂',
cases spec with x,
use x, exact evaln_mono p₃ spec_h,
intro h₅,cases h₅ with x,
use x,
have h₆ : ∃ k, x ∈ evaln k (of_nat_code n) 0,
use (max_halt n), exact h₅_h,
rw evaln_complete, exact h₆,
have p₁ : computable (λ n, φ ( α.1 (n+1))),
exact computable.comp h (computable.comp h₀ computable.succ),
have p₂ : computable(λn, max_halt n),
simp[max_halt], exact computable₂.comp primrec.nat_max.to_comp computable.id p₁,
have p₃ : computable(λ n, of_nat_code n),
rw ← of_nat_code_eq, exact computable.of_nat code,
let evalnmap:= λ (a : (ℕ × code) × ℕ), evaln a.1.1 a.1.2 a.2,
have p₄ : computable(evalnmap),
exact evaln_prim.to_comp,
let evalnmap':= λ (a : ℕ × code) , evalnmap (⟨ a, 0⟩),
have p₅ : computable(evalnmap'),
exact computable.comp p₄ (computable.pair computable.id (primrec.to_comp (primrec₂.const 0))),
let E:= λ n, evalnmap' (((max_halt n), (of_nat_code n))),
have p₆ : computable E,
simp[E], exact computable.comp p₅ (computable.pair p₂ p₃),
simp[E] at p₆,simp[evalnmap'] at p₆, simp[evalnmap] at p₆, simp at p₆,
have p₇ : computable_pred (λ n, option.is_some (evaln (max_halt n) (of_nat_code n) 0)),
simp[computable_pred],
refine ⟨by apply_instance, _⟩,
exact computable.comp primrec.option_is_some.to_comp p₆,
have p₈ : ∀ n,option.is_some (evaln (max_halt n) (of_nat_code n) 0) ↔ (∃ x, x ∈ evaln (max_halt n) (of_nat_code n) 0) ,
intros,exact option.is_some_iff_exists,
have p₉ : computable_pred(λn, ∃ x, x ∈ evaln (max_halt n) (of_nat_code n) 0),
exact computable_pred.of_eq p₇ p₈,
have q₁: computable_pred(λ n, ∃ (x : ℕ), x ∈ (of_nat_code n).eval 0),
exact computable_pred.of_eq p₉ h₆,
have q₂ : ∀ n ,(∃ (x : ℕ), x ∈ (of_nat_code n).eval 0) ↔ ((of_nat_code n).eval 0).dom,
intros, rw ←  dom_iff_mem,
have q₃ : computable_pred( λ n, ((of_nat_code n).eval 0).dom),
exact computable_pred.of_eq q₁ q₂,
have q₄ : computable_pred(λ c : code, ((eval (of_nat_code (encode_code c))) 0).dom),
casesI q₃,
refine ⟨by apply_instance, _⟩,
rw ← encode_code_eq,
exact computable.comp q₃_h computable.encode,
rw ← encode_code_eq at q₄,rw ← of_nat_code_eq at q₄, simp at q₄,
exact (computable_pred.halting_problem 0) q₄,
end 

