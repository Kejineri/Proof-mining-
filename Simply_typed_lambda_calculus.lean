import data.equiv.fin
import data.finset.basic
import logic.function.basic
universes u u' v
variables {α : Type u} 
variables {γ : Type v}
variables {β : Type u'} {n : ℕ} 
open classical
local attribute [instance] prop_decidable
/-- `term α n` is the type of terms with free variables indexed by `α`  -/
inductive term (α : Type u) : Type (max u u')
| var {} : ∀ (a : α), term
| abstraction (i: α ) (M : term ) : term 
| application (M N : term ) : term 
export term
local notation `[`M`(`N`)``]` := term.application M N
local notation `[``λ` `x_` i `.` M `)``]` := term.abstraction i M

@[reducible] def BV {α: Type u'} (M : term α ) : set α :=  term.rec_on M (λ i, ∅)(λ i M BVM, set.union BVM ({i}))(λ M N BVM BVN, set.union BVM BVN)
@[reducible]def  FV {α: Type u'} (M : term α ) : set α:=  term.rec_on M (λ i, {i})(λ i M FVM, set.diff FVM ({i}))(λ M N FVM FVN, set.union FVM FVN)
noncomputable def sub {α: Type u'} (M L : term α)(i:α)(h: i ∈ (FV M)): term α:= term.rec_on M (λ j, ite (i = j) L (term.var j)) (λ j M subM, ite (i = j) (term.abstraction j M ) (term.abstraction j subM))(λ M N subM subN, (term.application subM subN))

inductive type (β : Type u'): Type (max u u')
| base {} : ∀ (b : β), type
| arrow (σ  τ : type ) : type

def typing : ∀ {l} (M: term α ) (T :type β) (Γ_vars : fin l → α ) (Γ_types : fin l → (type β))(h : function.injective Γ_vars), Prop
| l (var i) T Γ_vars Γ_types h  := ∃ (k: fin l),(Γ_vars k = i)∧ (Γ_types k = T)
| l (abstraction i M) (type.base j) Γ_vars Γ_types h := false 
| l (abstraction i M) (type.arrow σ  τ ) Γ_vars Γ_types h := ∃(p : @function.injective (fin (l+1)) α (fin.snoc Γ_vars i)), typing M τ (fin.snoc Γ_vars i) (fin.snoc Γ_types σ) p
| l (application M N) T Γ_vars Γ_types h := ∃ σ, (typing M (type.arrow σ T) Γ_vars Γ_types h) ∧ (typing N σ Γ_vars Γ_types h)

 
def has_type_in_contex {l:ℕ } (Γ: (fin l → α) × (fin l → (type β))) (M: term α )(T :type β):= ∃(h:function.injective Γ.1),(typing M T Γ.1 Γ.2 h)
local notation Γ`⊢`M`:`T := has_type_in_contex Γ M T 


