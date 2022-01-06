import data.finset.basic
import data.vector

import tactic.linarith

def tofinset' : ∀ {n : ℕ} {α : Type} [decidable_eq α], vector α n -> finset α
| 0 _ _ vec := ∅
| (nat.succ n) α eq_dec_inst vec := 
  let union := (@finset.has_union α eq_dec_inst).union 
  in union (@tofinset' n α eq_dec_inst (vec.tail)) (singleton (vec.head))

lemma vec_head_in_finset : ∀ {n : ℕ} {α : Type} [inst : decidable_eq α] (vec : vector α (n+1)),
              vec.head ∈ @tofinset' (n+1) α inst vec :=
  begin
    intros n α inst vec,
    rw tofinset',
    apply finset.mem_union.2,
    exact or.inr (finset.mem_singleton_self vec.head),
  end

lemma tl_finset_subset_vec_finset : 
  ∀ {n : ℕ} {α : Type} [inst : decidable_eq α] (vec : vector α (n+1)),
    @tofinset' n α inst vec.tail ⊆ @tofinset' (n+1) α inst vec :=
  begin
    intros n α inst vec,
    rw tofinset',
    exact @finset.subset_union_left α inst (@tofinset' n α inst vec.tail) _,
  end

def tofinset {n : ℕ} {α : Type} [α_eq_dec : decidable_eq α] (f : fin n → α) : finset α :=
      tofinset' (vector.of_fn f)

def default_vals : ∀ {α : Type} {n : ℕ}, α → vector α n 
| α 0 _ := vector.nil
| α (nat.succ n) a := vector.cons a (default_vals a)

lemma ord_lem : ∀ (z : ℕ) {x y : ℕ}, x ≤ y → x < 1 + z + y :=
  begin
    intros x y z x_leq_y,
    linarith, 
  end

lemma of_fn_lemma : ∀ {α : Type} {n : ℕ} (f g : fin n → α),
        (∀ i : fin n, f i = g i) → list.of_fn f = list.of_fn g :=
  begin
    intros α n f g forall_i_f_eq_g,
    induction n,
    rw list.of_fn_zero f,
    rw list.of_fn_zero g,
    rw list.of_fn_succ f,
    rw list.of_fn_succ g,
    rw forall_i_f_eq_g 0,
    rw (list.cons_inj (g 0)).2,
    apply n_ih (λi, f i.succ) (λi, g i.succ),
    intro i,
    change f i.succ = g i.succ,
    exact forall_i_f_eq_g i.succ,
  end 