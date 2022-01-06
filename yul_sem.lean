
import data.finset.basic
import data.nat.basic
import init.data.fin.ops
import init.data.option.basic

import .yul_cmd

namespace YulSemantics

open YulCommands
open YulCommands.TermType
open YulCommands.IsInFunc
open YulCommands.IsInFor
open YulCommands.YulTerm

variable τ : Type
variable Γ : FTContext

inductive Mode : IsInFor → IsInFunc → Type
  | NormMode : ∀ {b : IsInFor} {b' : IsInFunc}, Mode b b'
  | BreakMode  : ∀ {b' : IsInFunc}, Mode NestedInFor b' 
  | ContinueMode : ∀ {b' : IsInFunc}, Mode NestedInFor b'
  | LeaveMode : ∀ {b : IsInFor}, Mode b InFunc
  | TermMode : ∀ {b : IsInFor} {b' : IsInFunc}, Mode b b'

open Mode

def liftMode : 
      ∀ {b : IsInFor} {b' : IsInFunc}, 
    Mode NotNestedInFor NotInFunc → Mode b b' 
| _ _ NormMode := NormMode
| _ _ TermMode := TermMode

def mode_eq : ∀ {b : IsInFor} {b' : IsInFunc}, Mode b b' -> Mode b b' -> Prop 
| _ _ NormMode NormMode := true
| _ _ BreakMode BreakMode := true
| _ _ ContinueMode ContinueMode := true
| _ _ LeaveMode LeaveMode := true
| _ _ TermMode TermMode := true
| _ _ BreakMode NormMode := false
| _ _ ContinueMode NormMode := false
| _ _ LeaveMode NormMode := false
| _ _ TermMode NormMode := false
| _ _ NormMode BreakMode := false
| _ _ ContinueMode BreakMode := false
| _ _ LeaveMode BreakMode := false
| _ _ TermMode BreakMode := false
| _ _ NormMode ContinueMode := false
| _ _ BreakMode ContinueMode := false
| _ _ LeaveMode ContinueMode := false
| _ _ TermMode ContinueMode := false
| _ _ NormMode LeaveMode := false
| _ _ BreakMode LeaveMode := false
| _ _ ContinueMode LeaveMode := false
| _ _ TermMode LeaveMode := false
| _ _ NormMode TermMode := false
| _ _ BreakMode TermMode := false
| _ _ ContinueMode TermMode := false
| _ _ LeaveMode TermMode := false


instance (b : IsInFor) (b' : IsInFunc) (a : Mode b b') (b : Mode b b') : decidable (mode_eq a b) :=
  begin
    cases a,
    repeat {
      cases b,
      repeat {
        rw mode_eq,
        apply decidable.is_false,
        intro f,
        exact f,
      },
      rw mode_eq,
      apply decidable.is_true,
      trivial,
    },
  end

def cast_not_in_for_mode : ∀ {b : IsInFor} {b' : IsInFunc}, Mode NotNestedInFor b' → Mode b b' :=
  begin
    intros b b' mode,
    cases mode,
    exact NormMode,
    exact LeaveMode,
    exact TermMode,
  end

def cast_not_in_func_mode : ∀ {b : IsInFor} {b' : IsInFunc}, Mode b NotInFunc → Mode b b' :=
  begin
    intros b b' mode,
    cases mode,
    exact NormMode,
    exact BreakMode,
    exact ContinueMode,
    exact TermMode,
  end


def FDef (n : ℕ) (m : ℕ)  := 
  Σ (arg_ids : vector Identifier n) (ret_args : vector Identifier m) (fin_args : finset Identifier), 
    YulTerm Γ 
      (BlockList 
        (tofinset' arg_ids ∪ tofinset' ret_args) 
        (fin_args ∪ tofinset' ret_args) 
        NotNestedInFor
        InFunc
      )

/- 
   FPrim n m primState is the type of state transformers which
   can fail over primState with arity n and returning m values.
-/

def FPrim (n : ℕ) (m : ℕ) :=
  vector Literal n → τ → option (τ × vector Literal m × Mode NotNestedInFor NotInFunc)

def FImpl (Γ : FTContext) := 
  ∀ i : Identifier, ∀ {n m : ℕ}, Γ i = some (n,m) → FDef Γ n m ⊕ FPrim τ n m

def YulState (Γ : FTContext) (vars : finset Identifier) := 
  VarStore vars × FImpl τ Γ × τ

def merge_scopes : ∀ {vars_outer vars_inner : finset Identifier},
   VarStore vars_outer → VarStore vars_inner → VarStore (vars_inner ∪ vars_outer)
| vars_outer vars_inner vso vsi i i_in_vo_u_vi := 
    dite (i ∈ vars_inner)
      (λ i_in_inner, vsi i i_in_inner)
      (λi_n_in_inner, 
        dite (i ∈ vars_outer)
        (λi_in_outer, vso i i_in_outer)
        (λi_n_in_outer, 
          let i_n_in_vo_u_vi : ¬  (i ∈ vars_inner ∪ vars_outer) := 
            begin
              intro i_in_vo_u_vi,
              cases finset.mem_union.1 i_in_vo_u_vi with h,
              exact (i_n_in_inner h),
              exact (i_n_in_outer h),
            end
          in absurd i_in_vo_u_vi i_n_in_vo_u_vi
        )
      )

def split_scope : ∀ {vars_inner vars_outer : finset Identifier}, 
  VarStore vars_outer → VarStore (vars_outer ∪ vars_inner) → 
  (VarStore vars_outer × VarStore vars_inner)
| vars_inner vars_outer outer_σ merged_σ' :=
  let outer_σ' : VarStore vars_outer :=
        λ i i_in_o, 
          let i_in_o_u_i : i ∈ vars_outer ∪ vars_inner :=
            begin
              apply finset.mem_union.2,
              exact (or.inl i_in_o),
            end
          in merged_σ' i i_in_o_u_i,
      inner_σ' : VarStore vars_inner :=
          λ i i_in_i, 
            let i_in_o_u_i : i ∈ vars_outer ∪ vars_inner :=
            begin
              apply finset.mem_union.2,
              exact (or.inr i_in_i),
            end
          in merged_σ' i i_in_o_u_i
  in (outer_σ', inner_σ')

def extend_var_store : 
  ∀ {vars : finset Identifier} {n : ℕ} (arg_ids : vector Identifier n) (arg_vals : vector Literal n), 
  VarStore vars → VarStore (vars ∪ tofinset' arg_ids)
  | vars 0 _ _ σ i i_in_vars_u_ids := 
    σ i 
      begin
        rw tofinset' at i_in_vars_u_ids,
        rw finset.union_empty at i_in_vars_u_ids,
        exact i_in_vars_u_ids,
      end
  | vars (nat.succ n) arg_ids arg_vals σ i i_in_vars_u_ids :=
    dite (i = arg_ids.head)
        (λ_, arg_vals.head)
      (λarg_id_neq_i, 
        let i_in_vars_u_ids' : i ∈ vars ∪ tofinset' (arg_ids.tail) :=
              begin
                rw finset.mem_union at i_in_vars_u_ids,
                cases i_in_vars_u_ids,
                apply finset.mem_union.2,
                exact (or.inl i_in_vars_u_ids),
                rw tofinset' at i_in_vars_u_ids,
                rw finset.mem_union at i_in_vars_u_ids,
                cases i_in_vars_u_ids,
                apply finset.mem_union.2,
                exact (or.inr i_in_vars_u_ids),
                exfalso,
                exact arg_id_neq_i (finset.mem_singleton.1 i_in_vars_u_ids),
              end
        in @extend_var_store vars n arg_ids.tail arg_vals.tail σ i i_in_vars_u_ids')

def extract_vars : 
  ∀ {n : ℕ} {vars : finset Identifier}, 
    VarStore vars → ∀ (vec : vector Identifier n),
    tofinset' vec ⊆ vars → vector Literal n 
  | 0 _ _ _ _ := vector.nil
  | (nat.succ n) vars σ vec vec_finset_ss_vars :=
      let head_in_vars : vec.head ∈ vars :=
            by {
              exact finset.mem_of_subset 
                vec_finset_ss_vars 
                (vec_head_in_finset vec),
            },
          tail_ss_vars : tofinset' vec.tail ⊆ vars :=
            by {
              exact finset.subset.trans 
                (tl_finset_subset_vec_finset vec) 
                vec_finset_ss_vars,
            }
      in vector.cons (σ vec.head head_in_vars) 
          (@extract_vars n vars σ vec.tail tail_ss_vars)

def termSize : ∀ {t : TermType}, YulTerm Γ t → ℕ
| _ EmpCBlock := 0
| t blklst@(SeqCBlock _ cstmnt blklst') := 1 + termSize cstmnt
| _ (NestedScope _ _ _ blklst) := 1 + termSize blklst

| _ (CCase _ cblk swtchbody) := 1 + termSize swtchbody
| _ (CDefault cblk) := 0
| _ CNone := 0

| _ (CFunctionCall _ n _ arg_exprs) := 1 + list.sum (list.of_fn (λ i : fin n, 1 + termSize (arg_exprs i)))
| _ (CId _ _) := 0
| _ (CLit _) := 0
| _ (Scope _ _ _ _ cstmnt) := 1 + termSize cstmnt
| _ (Result _) := 0

| _ (CBlock cblk) := 1 + termSize cblk
| _ (CVariableDeclarationAss _ _ cexpr) := 1 + termSize cexpr
| _ (CVariableDeclaration n new_vars) := 0
| _ (CAssignment _ _ _ cexpr) := 1 + termSize cexpr 
| _ (CIf cexpr cblk) := 1 + termSize cexpr
| _ (CExpressionStatement cexpr) := 1 + termSize cexpr 
| _ (CSwitch cexpr swtchbody) := 1 + termSize cexpr 
| _ (CFor _ _ _ init cond body post) := 0
| _ CBreak := 0
| _ CContinue := 0
| _ CLeave := 0
| _ (ForExecInit _ _ _ _ _ _ _ _ eval_init) := 1 + termSize eval_init
| _ (ForCheckCond _ _ _ _ _ _ _ eval_cond) := 1 + termSize eval_cond 
| _ (ForExecBody _ _ _ _ _ _ _ _ _ eval_loop) := 1 + termSize eval_loop
| _ (ForExecPost _ _ _ _ _ _ _ _ eval_post) := 1 + termSize eval_post
| _ Skip := 0

def evalMetric :
     (psum
       (Σ' {vars vars'' : finset Identifier} {b : IsInFor} {b' : IsInFunc}
          (blklst : YulTerm Γ (BlockList vars vars'' b b')) (ᾰ : ¬is_empcblock Γ blklst),
          YulState τ Γ vars)
       (psum
          (Σ' {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc} (blk : YulTerm Γ (CBlock vars b b'))
             (ᾰ : ¬is_empblock Γ blk),
             YulState τ Γ vars)
          (psum
             (Σ' {vars : finset Identifier} {n : ℕ} (cexprs : vector (YulTerm Γ (CExpr vars 1)) n)
                (ᾰ : ¬are_args_reduced Γ cexprs),
                YulState τ Γ vars)
             (psum
                (Σ' {vars : finset Identifier} {n : ℕ} (cexpr : YulTerm Γ (CExpr vars n))
                   (ᾰ : ¬is_result Γ cexpr),
                   YulState τ Γ vars)
                (Σ' {vars vars'' : finset Identifier} {b : IsInFor} {b' : IsInFunc}
                   (cstmnt : YulTerm Γ (CStatement vars vars'' b b')) (ᾰ : ¬is_skip Γ cstmnt),
                   YulState τ Γ vars))))) → ℕ
| (psum.inl ⟨_, _, _, _, blklst, _, _⟩) := termSize Γ blklst
| (psum.inr (psum.inl ⟨_, _, _, blk, _, _⟩)) := termSize Γ blk
| (psum.inr (psum.inr (psum.inl ⟨_, n, cexprs, _, _⟩))) := list.sum (list.of_fn (λ i : fin n, 1 + termSize Γ (cexprs.nth i)))
| (psum.inr (psum.inr (psum.inr (psum.inl ⟨_, _, cexpr, _, _⟩)))) := termSize Γ cexpr
| (psum.inr (psum.inr (psum.inr (psum.inr ⟨_, _, _, _, cstmnt, _, _⟩)))) := termSize Γ cstmnt

mutual def evalBlockList, evalCBlock, reduce_last, evalCExpr, evalCStatement

with evalBlockList : 
  ∀ {vars vars'' : finset Identifier} {b : IsInFor} {b' : IsInFunc} 
      (blklst : YulTerm Γ (BlockList vars vars'' b b')),
    ¬is_empcblock Γ blklst → YulState τ Γ vars →
    option 
      Σ vars' : finset Identifier,
        pprod 
          (vars ⊆ vars') 
          (YulState τ Γ vars' × YulTerm Γ (BlockList vars' vars'' b b') × Mode b b')
      
| _ _ _ _ blklst@(EmpCBlock) n_is_empcblock _ :=
    let is_empcblock : is_empcblock Γ blklst :=
          begin
            rw is_empcblock,
            trivial,
          end
    in absurd is_empcblock n_is_empcblock
| vars vars'' b b' blklst@(SeqCBlock vars' cstmnt cblklst') n_is_empcblock st :=
  have termSize Γ cstmnt < termSize Γ blklst,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_skip Γ cstmnt)
      (λcstmnt_is_skip,
        pure $
          sigma.mk vars 
            ⟨
              finset.subset.refl vars,
              (
                st, 
                eq.rec cblklst' (is_skip_imp_vars_eq_vars' Γ cstmnt_is_skip), 
                Mode.NormMode
              )
            ⟩
      )
      (λcstmnt_n_is_skip,
        do
        (sigma.mk vars'₁ ⟨p, (st', cstmnt', mode)⟩) ← evalCStatement cstmnt cstmnt_n_is_skip st,
        pure $
          sigma.mk vars'₁
            ⟨
              p,
              (st', SeqCBlock vars' cstmnt' cblklst', mode)
            ⟩
  )

with evalCBlock : 
  ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc} 
      (blk : YulTerm Γ (CBlock vars b b')),
    ¬is_empblock Γ blk → YulState τ Γ vars →
    option (YulState τ Γ vars × YulTerm Γ (CBlock vars b b') × Mode b b') 
| vars b b' cblk@(NestedScope inner_vars inner_vars'' inner_σ blklst) n_is_empblock st :=
  have termSize Γ blklst < termSize Γ cblk,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  }, do
  let inner_st : YulState τ Γ (inner_vars ∪ vars) := 
    (merge_scopes st.1 inner_σ, st.2),
  let blklst_n_is_empcblock : ¬ is_empcblock Γ blklst :=
    by {
      rw is_empblock at n_is_empblock,
      exact n_is_empblock,
    },
  (sigma.mk all_vars' ⟨p, (inner_st', blklst', mode)⟩) ← 
    evalBlockList blklst blklst_n_is_empcblock inner_st,
  let inner_vars' := all_vars' \ vars,
  let p' : vars ⊆ all_vars' := by {exact finset.union_subset_right p},
  let all_vars'_cast_p : all_vars' = vars ∪ (all_vars' \ vars) :=
    by {
      apply eq.symm,
      exact finset.union_sdiff_of_subset p',
    },
  let cast_all_vars' : VarStore (vars ∪ (all_vars' \ vars)) := 
    eq.rec inner_st'.1 all_vars'_cast_p,
  let (outer_σ', inner_σ') := split_scope st.1 cast_all_vars',
  let st' := (outer_σ', inner_st'.2),
  let blklst'_cast_p : all_vars' = all_vars' \ vars ∪ vars :=
    by {
      apply eq.symm,
      exact finset.sdiff_union_of_subset p',
    },
  let cast_blklst' : YulTerm Γ (BlockList (all_vars' \ vars ∪ vars) (inner_vars'' ∪ vars) b b') :=
    eq.rec blklst' blklst'_cast_p,
  pure (st', NestedScope (all_vars' \ vars) inner_vars'' inner_σ' cast_blklst', mode)

with reduce_last : 
  ∀ {vars : finset Identifier} {n : ℕ} 
    (cexprs : vector (YulTerm Γ (CExpr vars 1)) n), 
      ¬(are_args_reduced Γ cexprs) → YulState τ Γ vars → 
      option (YulState τ Γ vars × vector (YulTerm Γ (CExpr vars 1)) n × Mode NotNestedInFor NotInFunc)
| vars 0 _ p _ := absurd (@nil_reduced Γ vars) p
| vars (nat.succ n) cexprs n_is_red st :=
  let cexpr' : vector (YulTerm Γ (CExpr vars 1)) n := cexprs.tail in
  have termSize Γ cexprs.head < list.sum (list.of_fn (λ i : fin (nat.succ n), 1 + termSize Γ (cexprs.nth i))),
  by {
    rw list.sum,
    rw (list.foldl_eq_foldr nat.comm_semiring.add_comm 
          nat.comm_semiring.add_assoc 0 
            (list.of_fn (λ (i : fin n.succ), 1 + termSize Γ (cexprs.nth i)))),
    rw list.of_fn_succ _,
    rw list.foldr,
    rw vector.nth_zero cexprs,
    linarith,
  },
  have list.sum (list.of_fn (λ i : fin n, 1 + termSize Γ (cexprs.tail.nth i))) 
          < list.sum (list.of_fn (λ i : fin (nat.succ n), 1 + termSize Γ (cexprs.nth i))),
  by {
    rw list.sum,
    rw list.of_fn_succ _,
    rw (list.foldl_eq_foldr nat.comm_semiring.add_comm 
          nat.comm_semiring.add_assoc 0 
            ((1 + termSize Γ (cexprs.nth 0)) :: list.of_fn (λ (i : fin n), 1 + termSize Γ (cexprs.nth i.succ)))),
    rw list.foldr,
    apply (ord_lem (termSize Γ (cexprs.nth 0))),
    rw ←(list.foldl_eq_foldr nat.comm_semiring.add_comm 
          nat.comm_semiring.add_assoc 0 
            (list.of_fn (λ (i : fin n), 1 + termSize Γ (cexprs.nth i.succ)))),
    change list.foldl has_add.add 0 (list.of_fn (λ (i : fin n), 1 + termSize Γ (cexprs.tail.nth i))) ≤
            list.foldl has_add.add 0 (list.of_fn (λ (i : fin n), 1 + termSize Γ (cexprs.nth i.succ))),
    apply nat.le_of_eq,
    apply (@congr_arg (list ℕ) ℕ
            (list.of_fn (λ (i : fin n), 1 + termSize Γ (cexprs.tail.nth i)))
              (list.of_fn (λ (i : fin n), 1 + termSize Γ (cexprs.nth i.succ)))
                (list.foldl has_add.add 0)),
    apply (of_fn_lemma _ _),
    intro i,
    rw vector.nth_tail_succ cexprs i,
  },
  let arg_vec' : vector (YulTerm Γ (CExpr vars 1)) n := cexprs.tail
  in dite (are_args_reduced Γ cexprs.tail)
      (λtl_red, do
        let res : ¬is_result Γ cexprs.head :=
              begin
                rw ←(vector.cons_head_tail cexprs) at n_is_red,
                exact reduced_and_n_tail_reduced_imp_n_lit 
                        Γ cexprs.head cexprs.tail n_is_red tl_red,
              end,
        (st', arg', mode) ← evalCExpr cexprs.head res st,
        pure (st', vector.cons arg' arg_vec', mode)
      )
      (λn_tl_red, do
        (st', ⟨args', p⟩, mode) ← @reduce_last vars n cexpr' n_tl_red st,
        pure 
            (
              st', 
              ⟨ 
                cexprs.head :: args', 
                (by {
                  rw list.length,
                  rw p,
                } : (cexprs.head :: args').length = nat.succ n) 
              ⟩, 
              mode
            )
      )

with evalCExpr : 
  ∀ {vars : finset Identifier} {n : ℕ} (cexpr : YulTerm Γ (CExpr vars n)),
    ¬is_result Γ cexpr → YulState τ Γ vars → 
    option (YulState τ Γ vars × YulTerm Γ (CExpr vars n) × Mode NotNestedInFor NotInFunc)
  | _ _ cexpr@(Result _) n_is_res _ := 
    let is_res : is_result Γ cexpr :=
          begin
            rw is_result,
            trivial,
          end
    in absurd is_res n_is_res
  | _ 1 cexpr@(CLit l) _ st := 
    pure 
        (
          st, 
          Result
            ⟨ 
              [l], 
              by {
                repeat {
                  rw list.length,
                },
              }
            ⟩, 
          Mode.NormMode
        )
| _ 1 (CId i i_in_vars) _ st :=
      let l := st.1 i i_in_vars
      in pure (st, CLit l, Mode.NormMode)
| _ _ cexpr@(CFunctionCall f_id n ar_match arg_map) _ st :=
  let arg_vec := (vector.of_fn arg_map)
  in 
    have list.sum (list.of_fn (λ i : fin n, 1 + termSize Γ ((vector.of_fn arg_map).nth i))) < termSize Γ cexpr,
      by {
        rw termSize,
        apply (ord_lem 0),
        apply @nat.le.intro _ _ 0,
        rw (nat_add_zero  _),
        apply congr_arg list.sum,
        apply (of_fn_lemma _ _),
        intros i,
        rw vector.nth_of_fn arg_map i,
      },
    dite (are_args_reduced Γ (vector.of_fn arg_map))
      (λ is_red, 
          let arg_vals := get_lits Γ (vector.of_fn arg_map) is_red,
              σ := st.1,
              fimpl := st.2.1,
              μ := st.2.2
          in 
            let f_impl := fimpl f_id ar_match
            in match f_impl with
                | sum.inl (sigma.mk arg_ids (sigma.mk ret_args (sigma.mk fin_args fbody))) := 
                    let inner_σ : VarStore (tofinset' arg_ids ∪ tofinset' ret_args):= 
                          extend_var_store ret_args (default_vals literal_zero)
                            (eq.rec (extend_var_store arg_ids arg_vals empStore)
                              (finset.empty_union $ tofinset' arg_ids))
                    in pure 
                        (st, Scope (tofinset' arg_ids) fin_args ret_args inner_σ fbody, Mode.NormMode)
                | sum.inr prim_def := do
                    (μ', res_vec, mode) ← prim_def arg_vals μ,
                    let st' := (σ, fimpl, μ'),
                    pure (st', Result res_vec, mode)
               end
      )
      (λ np, do
        (st', arg_vec', mode) ← reduce_last (vector.of_fn arg_map) np st,
        pure (st', CFunctionCall f_id n ar_match arg_vec'.nth, mode)
      )
| _ _ cexpr@(Scope vars_inner vars_fin ret_ids inner_σ blklst) _ st :=
  have termSize Γ blklst < termSize Γ cexpr,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_empcblock Γ blklst)
      (λ_,  let res_vec := extract_vars inner_σ ret_ids
                            (by {
                              intros i i_in_finset,
                              apply finset.mem_union.2,
                              exact or.inr i_in_finset,
                            })
            in pure (st, Result res_vec, Mode.NormMode)
      )
      (λcstmnt_n_is_empcblock, do
        let inner_st := (inner_σ, st.2),
        (sigma.mk vars_inner' ⟨p, (inner_st', blklst', mode)⟩) ← 
          evalBlockList blklst cstmnt_n_is_empcblock inner_st,
        let st' := (st.1, inner_st'.2),
        let inner_σ' := inner_st'.1,
        let inner_σ'_cast_p : vars_inner' = vars_inner' ∪ tofinset' ret_ids :=
          begin
            apply finset.ext_iff.2,
            intro a,
            apply
              (iff_iff_implies_and_implies 
                (a ∈ vars_inner')
                (a ∈ vars_inner' ∪ tofinset' ret_ids)).2,
            split,
            intro a_in_vars_inner',
            apply finset.mem_union.2,
            exact or.inl a_in_vars_inner',
            intro a_in_vars_inner'_u_ret_ids,
            cases finset.mem_union.1 a_in_vars_inner'_u_ret_ids,
            exact h,
            exact (finset.union_subset_iff.1 p).2 h,
          end,
        let cast_inner_σ' : VarStore (vars_inner' ∪ tofinset' ret_ids) := 
          eq.rec inner_σ' inner_σ'_cast_p,
        let cast_blklst' : 
              YulTerm Γ (BlockList (vars_inner' ∪ tofinset' ret_ids) (vars_fin ∪ tofinset' ret_ids) NotNestedInFor InFunc) := 
            eq.rec blklst' inner_σ'_cast_p,
        pure $
          begin
            cases mode,
            exact (st', Scope vars_inner' vars_fin ret_ids cast_inner_σ' cast_blklst', NormMode),
            exact (st', Scope vars_inner' vars_inner' ret_ids cast_inner_σ' EmpCBlock, NormMode),
            exact (st', Scope vars_inner' vars_fin ret_ids cast_inner_σ' cast_blklst', TermMode),
          end
      )

with evalCStatement : 
  ∀ {vars vars'' : finset Identifier} {b : IsInFor} {b' : IsInFunc}
      (cstmnt : YulTerm Γ (CStatement vars vars'' b b')),
    ¬ is_skip Γ cstmnt → YulState τ Γ vars →
    option
      Σ vars' : finset Identifier,
        pprod
          (vars ⊆ vars')
          (YulState τ Γ vars' × YulTerm Γ (CStatement vars' vars'' b b') × Mode b b')
| _ _  _ _ cstmnt@Skip cstmnt_n_is_skip  _ :=
  let cstmnt_is_skip : is_skip Γ cstmnt :=
        begin
          rw is_skip,
          trivial,
        end
  in absurd cstmnt_is_skip cstmnt_n_is_skip
| vars _ _ _ cstmnt@(CBlock blk) _ st :=
  have termSize Γ blk < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_empblock Γ blk)
    (λ_, pure $
          sigma.mk vars 
            ⟨finset.subset.refl vars, (st, Skip, Mode.NormMode)⟩
    )
    (λblk_is_empblock, do
      (st', blk', mode) ← evalCBlock blk blk_is_empblock st,
      pure $
        sigma.mk vars 
          ⟨finset.subset.refl vars, (st', CBlock blk', mode)⟩
    )
| vars _ _ _ cstmnt@(CVariableDeclarationAss n new_vars cexpr) _ st :=
  have termSize Γ cexpr < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_result Γ cexpr)
    (λcexpr_is_result, 
      pure $
        sigma.mk (vars ∪ tofinset new_vars)
        ⟨
          by {
            intros var var_in_vars,
            apply finset.mem_union.2,
            exact or.inl var_in_vars,
          }, 
          (
            by {
              cases cexpr,
              repeat {
                exfalso,
                rw is_result at cexpr_is_result,
                exact cexpr_is_result,
              },
              rw tofinset,
              exact (extend_var_store (vector.of_fn new_vars) cexpr_ᾰ st.1, st.2),
            }, 
            Skip, 
            Mode.NormMode
          )
        ⟩
    )
    (λcexpr_n_is_result, do
      (st', cexpr', mode) ← evalCExpr cexpr cexpr_n_is_result st,
      pure $
        sigma.mk vars 
          ⟨
            finset.subset.refl vars, 
            (st', CVariableDeclarationAss n new_vars cexpr', liftMode mode)
          ⟩
    )
| vars _ _ _ cstmnt@(CVariableDeclaration n new_vars) _ st :=
  pure $ 
    sigma.mk (vars ∪ tofinset new_vars)
      ⟨
        by {
            intros var var_in_vars,
            apply finset.mem_union.2,
            exact or.inl var_in_vars,
          },
        (
          (extend_var_store (vector.of_fn new_vars) (default_vals literal_zero) st.1, st.2), 
          Skip, 
          Mode.NormMode
        )
      ⟩
| vars _ _ _ cstmnt@(CAssignment n ids p cexpr) _ st :=
  have termSize Γ cexpr < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_result Γ cexpr)
    (λcexpr_is_result, do
      let vars_eq_vars_u_ids : vars = vars ∪ tofinset' (vector.of_fn ids) :=
            begin
              rw tofinset at p,
              exact finset.left_eq_union_iff_subset.2 p,
            end,
      pure $
        sigma.mk vars
        ⟨
          finset.subset.refl vars, 
          (
            by {
              cases cexpr,
              repeat {
                exfalso,
                rw is_result at cexpr_is_result,
                exact cexpr_is_result,
              },
              have σ' := extend_var_store (vector.of_fn ids) cexpr_ᾰ st.1,
              rw ← vars_eq_vars_u_ids at σ',
              exact (σ', st.2),
            }, 
            Skip, 
            Mode.NormMode
          )
        ⟩
    )
    (λcexpr_n_is_result, do
      (st', cexpr', mode) ← evalCExpr cexpr cexpr_n_is_result st,
      pure $
        sigma.mk vars 
          ⟨
            finset.subset.refl vars, 
            (st', CAssignment n ids p cexpr', liftMode mode)
          ⟩
    )
| vars _ _ _ cstmnt@(CIf cond body) _ st :=
  have termSize Γ cond < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_result Γ cond)
    (λcond_is_result,
      pure $
        sigma.mk vars
          ⟨
            finset.subset.refl vars,
            (
              st, 
              by {
                cases cond,
                repeat {
                  exfalso,
                  rw is_result at cond_is_result,
                  exact cond_is_result,
                },
                cases cond_ᾰ.head,
                cases val,
                exact Skip,
                exact CBlock body,
              }, 
              Mode.NormMode
            )
          ⟩
    )
    (λcond_n_is_result, do
      (st', cond', mode) ← evalCExpr cond cond_n_is_result st,
      pure $
        sigma.mk vars
          ⟨
            finset.subset.refl vars,
            (st', CIf cond' body, liftMode mode)
          ⟩
    )
| vars _ _ _ cstmnt@(CExpressionStatement cexpr) _ st :=
  have termSize Γ cexpr < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_result Γ cexpr)
    (λ_, pure $
          sigma.mk vars 
            ⟨
              finset.subset.refl vars,
              (st, Skip, Mode.NormMode)
            ⟩
    )
    (λcexpr_n_is_result, do
      (st', cexpr', mode) ← evalCExpr cexpr cexpr_n_is_result st,
      pure $
        sigma.mk vars
          ⟨
            finset.subset.refl vars, 
            (st', CExpressionStatement cexpr', liftMode mode)
          ⟩
    )
| vars _ _ _ cstmnt@(CSwitch cexpr swtchbody) _ st :=
  have termSize Γ cexpr < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_result Γ cexpr)
    (λcexpr_is_result,
      let lit : Literal := (to_literal Γ cexpr cexpr_is_result).head,
          cblk := getCase Γ lit swtchbody
      in pure $
          sigma.mk vars
            ⟨
              finset.subset.refl vars,
              (st, CBlock cblk, NormMode)
            ⟩
    )
    (λcexpr_n_is_result, do
      (st', cexpr', mode) ← evalCExpr cexpr cexpr_n_is_result st,
      pure $
        sigma.mk vars 
          ⟨
            finset.subset.refl vars, 
            (st', CSwitch cexpr' swtchbody, liftMode mode)
          ⟩
    )
| vars _ b b' (CFor inner_vars inner_vars' inner_vars'' init cond loop post) _ st :=
  pure $
    sigma.mk vars 
      ⟨
        finset.subset.refl vars,
        let eq_vars : vars = vars ∪ ∅ := eq.symm (finset.union_empty vars),
            init_cast : YulTerm Γ (BlockList (vars ∪ ∅) (vars ∪ inner_vars) NotNestedInFor b') := 
              @eq.rec (finset Identifier) vars 
                (λvs, YulTerm Γ (BlockList vs (vars ∪ inner_vars) NotNestedInFor b')) init (vars ∪ ∅)
                  eq_vars,
            cstmnt' : YulTerm Γ (CStatement vars vars b b') := 
              ForExecInit ∅ inner_vars inner_vars' inner_vars'' empStore cond loop post init_cast
        in (st, cstmnt', NormMode)
      ⟩
| vars _ _ b' CBreak _ st :=
  pure $
    sigma.mk vars 
      ⟨
          finset.subset.refl vars,
          (st, Skip, BreakMode)
      ⟩
| vars _ _ b' CContinue _ st :=
  pure $
    sigma.mk vars 
      ⟨
          finset.subset.refl vars,
          (st, Skip, ContinueMode)
      ⟩
| vars _ b _ CLeave _ st :=
  pure $
    sigma.mk vars 
      ⟨
          finset.subset.refl vars,
          (st, Skip, LeaveMode)
      ⟩
| vars _ b b' cstmnt@(ForExecInit curr_inner_vars inner_vars inner_vars' inner_vars'' σ cond loop post eval_init) _ st :=
  have termSize Γ eval_init < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_empcblock Γ eval_init)
    (λeval_init_is_empcblock, do
      let vars_eq_vars' := eq.symm $ is_empcblock_imp_vars_eq_vars' Γ eval_init_is_empcblock,
      pure $
        sigma.mk vars
          ⟨
            finset.subset.refl vars,
            (
              eq.rec st vars_eq_vars', 
              ForCheckCond curr_inner_vars inner_vars' inner_vars'' σ 
                (eq.rec cond vars_eq_vars') (eq.rec loop vars_eq_vars') post (eq.rec cond vars_eq_vars'), 
              NormMode
            )
          ⟩
    )
    (λeval_init_n_is_empcblock, do
      let inner_st : YulState τ Γ (vars ∪ curr_inner_vars) := 
            (merge_scopes σ st.1, st.2),
      (sigma.mk all_vars' ⟨p, (inner_st', eval_init', mode)⟩)  ← evalBlockList eval_init eval_init_n_is_empcblock inner_st,
      let p' : vars ⊆ all_vars' := by {exact finset.union_subset_left p},
      let all_vars'_cast_p : all_vars' = vars ∪ (all_vars' \ vars) :=
        by {
          apply eq.symm,
          exact finset.union_sdiff_of_subset p',
        },
      let cast_all_vars' : VarStore (vars ∪ (all_vars' \ vars)) := 
            eq.rec inner_st'.1 all_vars'_cast_p,
      let (outer_σ', inner_σ') := split_scope st.1 cast_all_vars',
      let st' := (outer_σ', inner_st'.2),
      let cast_eval_init' : YulTerm Γ (BlockList (vars ∪ (all_vars' \ vars)) (vars ∪ inner_vars) NotNestedInFor b') :=
            eq.rec eval_init' all_vars'_cast_p,
      pure $
        sigma.mk vars 
          ⟨
            finset.subset.refl vars,
            (
              st', 
              ForExecInit (all_vars' \ vars) inner_vars inner_vars' inner_vars'' inner_σ' cond loop post cast_eval_init', 
              cast_not_in_for_mode mode
            )
          ⟩
    )
| vars _ _ _ cstmnt@(ForCheckCond inner_vars inner_vars' inner_vars'' σ cond body post eval_cond) _ st :=
  have termSize Γ eval_cond < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_result Γ eval_cond)
    (λeval_cond_is_result,
        let lit : Literal := (to_literal Γ eval_cond eval_cond_is_result).head
        in pure $
            sigma.mk vars 
              ⟨
                finset.subset.refl vars,
                (
                  st,
                  if lit ≠ literal_zero
                  then ForExecBody inner_vars inner_vars inner_vars' inner_vars'' σ 
                        (finset.subset.refl (vars ∪ inner_vars)) cond body post body
                  else Skip,
                  NormMode
                )
              ⟩
    )
    (λeval_cond_n_is_result, do
      let inner_st : YulState τ Γ (vars ∪ inner_vars) := 
             (merge_scopes σ st.1, st.2),
      (inner_st', eval_cond', mode) ← evalCExpr eval_cond eval_cond_n_is_result inner_st,
      let (outer_σ', inner_σ') := split_scope st.1 inner_st'.1,
      pure $
        sigma.mk vars 
          ⟨
            finset.subset.refl vars,
            (
              (outer_σ', inner_st'.2), 
              ForCheckCond inner_vars inner_vars' inner_vars'' σ cond body post eval_cond', 
              cast_not_in_func_mode (cast_not_in_for_mode mode)
            )
          ⟩
    )
| vars _ b b' cstmnt@(ForExecBody curr_inner_vars inner_vars inner_vars' inner_vars'' σ ss_p cond body post eval_body) _ st :=
  have termSize Γ eval_body < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_empcblock Γ eval_body)
    (λeval_body_is_empcblock, do
      let vars_eq_vars' := eq.symm $ is_empcblock_imp_vars_eq_vars' Γ eval_body_is_empcblock,
      pure $
        sigma.mk vars
          ⟨
            finset.subset.refl vars,
            (
              eq.rec st vars_eq_vars', 
              ForExecPost curr_inner_vars inner_vars inner_vars' inner_vars'' σ 
                (eq.rec cond vars_eq_vars') (eq.rec body vars_eq_vars') post (eq.rec post vars_eq_vars'), 
              NormMode
            )
          ⟩
    )
    (λeval_body_n_is_empcblock, do
      let inner_st : YulState τ Γ (vars ∪ curr_inner_vars) := 
            (merge_scopes σ st.1, st.2),
      (sigma.mk all_vars' ⟨p, (inner_st', eval_body', mode)⟩) ← evalBlockList eval_body eval_body_n_is_empcblock inner_st,
      let p' : vars ⊆ all_vars' := by {exact finset.union_subset_left p},
      let all_vars'_cast_p : all_vars' = vars ∪ (all_vars' \ vars) :=
        by {
          apply eq.symm,
          exact finset.union_sdiff_of_subset p',
        },
      let cast_all_vars' : VarStore (vars ∪ (all_vars' \ vars)) := 
            eq.rec inner_st'.1 all_vars'_cast_p,
      let (outer_σ', inner_σ') := split_scope st.1 cast_all_vars',
      let st' := (outer_σ', inner_st'.2),
      let cast_eval_body' : YulTerm Γ (BlockList (vars ∪ (all_vars' \ vars)) (vars ∪ inner_vars') NestedInFor b') :=
            eq.rec eval_body' all_vars'_cast_p,
      let ss_p' : vars ∪ inner_vars ⊆ vars ∪ (all_vars' \ vars) := 
            begin
              apply (finset.subset.trans ss_p),
              rw ←all_vars'_cast_p,
              exact p,
            end,
      begin
        apply some,
        apply sigma.mk vars,
        apply (⟨finset.subset.refl vars, _⟩ : 
          pprod (vars ⊆ vars) (YulState τ Γ vars × YulTerm Γ (CStatement vars vars b b') × Mode b b')),
        apply (st', _),
        clear _do_match _let_match,
        cases mode,
        exact (
                ForExecBody (all_vars' \ vars) inner_vars inner_vars' inner_vars'' 
                  inner_σ' ss_p' cond body post cast_eval_body',
                NormMode
              ),
        exact (Skip, NormMode),
        apply (ForCheckCond (all_vars' \ vars) inner_vars' inner_vars'' inner_σ' _ _ _ _, NormMode),
        have cond_framed := frame Γ (vars ∪ (all_vars' \ vars)) cond,
        rw frame_TermType at cond_framed,
        rw finset.right_eq_union_iff_subset.2 ss_p',
        exact cond_framed,
        have body_framed := frame Γ (vars ∪ (all_vars' \ vars)) body,
        rw frame_TermType at body_framed,
        rw finset.right_eq_union_iff_subset.2 ss_p',
        rw finset.left_eq_union_iff_subset.2
            (term_scope_monotonic Γ eval_body' 
                      all_vars' 
                      (vars ∪ inner_vars') _),
        rw ←all_vars'_cast_p at body_framed,
        rw ←all_vars'_cast_p,
        exact body_framed,
        rw getVariableUpdate,
        exact post,
        have cond_framed := frame Γ (vars ∪ (all_vars' \ vars)) cond,
        rw frame_TermType at cond_framed,
        rw finset.right_eq_union_iff_subset.2 ss_p',
        exact cond_framed,
        exact (
                ForExecBody (all_vars' \ vars) inner_vars inner_vars' inner_vars'' 
                  inner_σ' ss_p' cond body post cast_eval_body',
                LeaveMode
              ),
        exact (
                ForExecBody (all_vars' \ vars) inner_vars inner_vars' inner_vars'' 
                  inner_σ' ss_p' cond body post cast_eval_body',
                TermMode
              ),
      end
    )
| vars _ _ b' cstmnt@(ForExecPost curr_inner_vars inner_vars inner_vars' inner_vars'' σ cond body post eval_post) _ st := 
  have termSize Γ eval_post < termSize Γ cstmnt,
  by {
    repeat {
      rw termSize,
    },
    linarith,
  },
  dite (is_empcblock Γ eval_post)
    (λeval_post_is_empcblock, do
      let vars_eq_vars' := eq.symm $ is_empcblock_imp_vars_eq_vars' Γ eval_post_is_empcblock,
      pure $
        sigma.mk vars
          ⟨
            finset.subset.refl vars,
            (
              eq.rec st vars_eq_vars', 
              (begin
                apply (ForCheckCond curr_inner_vars curr_inner_vars curr_inner_vars σ),
                have cond_framed := frame Γ (vars ∪ inner_vars'') cond,
                rw ←vars_eq_vars',
                rw frame_TermType at cond_framed,
                rw (finset.right_eq_union_iff_subset.2 $
                    finset.subset.trans
                              (term_scope_monotonic Γ body
                                (vars ∪ inner_vars)
                                (vars ∪ inner_vars') _)
                              (term_scope_monotonic Γ post
                                (vars ∪ inner_vars')
                                (vars ∪ inner_vars'') _)),
                exact cond_framed,
                repeat {
                  rw getVariableUpdate,
                },
                have body_framed := frame Γ (vars ∪ inner_vars'') body,
                rw ←vars_eq_vars',
                rw frame_TermType at body_framed,
                rw ←(finset.right_eq_union_iff_subset.2 $
                      finset.subset.trans
                        (term_scope_monotonic Γ body
                          (vars ∪ inner_vars)
                          (vars ∪ inner_vars') 
                          _
                        )
                        (term_scope_monotonic Γ post
                          (vars ∪ inner_vars')
                          (vars ∪ inner_vars'') 
                          _
                        )
                     ) at body_framed,
                rw ←(finset.right_eq_union_iff_subset.2 $
                      (term_scope_monotonic Γ post
                        (vars ∪ inner_vars')
                        (vars ∪ inner_vars'') 
                        _
                      )
                    ) at body_framed,
                exact body_framed,
                repeat {
                  rw getVariableUpdate,
                },
                have post_framed := frame Γ (vars ∪ inner_vars'') post,
                rw ←vars_eq_vars',
                rw frame_TermType at post_framed,
                rw ←(finset.right_eq_union_iff_subset.2 $
                      (term_scope_monotonic Γ post
                        (vars ∪ inner_vars')
                        (vars ∪ inner_vars'') 
                        _
                      )
                    ) at post_framed,
                rw finset.union_self (vars ∪ inner_vars'') at post_framed,
                exact post_framed,
                repeat {
                  rw getVariableUpdate,
                },
                have cond_eval_framed := frame Γ (vars ∪ inner_vars'') cond,
                rw ←vars_eq_vars',
                rw frame_TermType at cond_eval_framed,
                rw (finset.right_eq_union_iff_subset.2 $
                    finset.subset.trans
                              (term_scope_monotonic Γ body
                                (vars ∪ inner_vars)
                                (vars ∪ inner_vars') _)
                              (term_scope_monotonic Γ post
                                (vars ∪ inner_vars')
                                (vars ∪ inner_vars'') _)),
                exact cond_eval_framed,
                repeat {
                  rw getVariableUpdate,
                },
              end),
              NormMode
            )
          ⟩
    )
    (λeval_post_n_is_empcblock, do
      let inner_st : YulState τ Γ (vars ∪ curr_inner_vars) := 
            (merge_scopes σ st.1, st.2),
      (sigma.mk all_vars' ⟨p, (inner_st', eval_post', mode)⟩) ← 
        evalBlockList eval_post eval_post_n_is_empcblock inner_st,
      let p' : vars ⊆ all_vars' := by {exact finset.union_subset_left p},
      let all_vars'_cast_p : all_vars' = vars ∪ (all_vars' \ vars) :=
      by {
        apply eq.symm,
        exact finset.union_sdiff_of_subset p',
      },
      let cast_all_vars' : VarStore (vars ∪ (all_vars' \ vars)) := 
            eq.rec inner_st'.1 all_vars'_cast_p,
      let (outer_σ', inner_σ') := split_scope st.1 cast_all_vars',
      let st' := (outer_σ', inner_st'.2),
      let cast_eval_post' : YulTerm Γ (BlockList (vars ∪ (all_vars' \ vars)) (vars ∪ inner_vars'') NotNestedInFor b') :=
            eq.rec eval_post' all_vars'_cast_p,
      pure $
        sigma.mk vars 
          ⟨
            finset.subset.refl vars,
            (
              st', 
              ForExecPost (all_vars' \ vars) inner_vars inner_vars' inner_vars'' inner_σ' cond body post cast_eval_post', 
              cast_not_in_for_mode mode
            )
          ⟩
    )
    
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (evalMetric τ Γ)⟩],
  dec_tac := `[assumption] }
  
end YulSemantics