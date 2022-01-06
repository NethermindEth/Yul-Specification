import .yul_ast
import .aux

import tactic.linarith

import data.finset.basic
import data.vector
import init.data.fin.ops
import init.data.list.basic


set_option class.instance_max_depth 100

def FTContext := Identifier → option (ℕ × ℕ)
def empΓ : FTContext := λ_, none 

def VarStore (vars : finset Identifier) := ∀ i : Identifier, (i ∈ vars) → Literal
def empStore : VarStore ∅
  | i i_in_emp := absurd i_in_emp (finset.not_mem_empty i)

namespace YulCommands

variable Γ : FTContext

inductive IsInFor : Type
| NestedInFor : IsInFor
| NotNestedInFor : IsInFor

inductive IsInFunc : Type
| InFunc : IsInFunc
| NotInFunc : IsInFunc

inductive TermType : Type
| BlockList :  finset Identifier → finset Identifier → IsInFor → IsInFunc → TermType
| CBlock : finset Identifier → IsInFor → IsInFunc → TermType
| SwitchBody : finset Identifier → IsInFor → IsInFunc → TermType
| CExpr : finset Identifier → ℕ → TermType
| CStatement : finset Identifier → finset Identifier → IsInFor → IsInFunc → TermType

open IsInFor
open IsInFunc
open TermType

inductive YulTerm : TermType → Type
| EmpCBlock : 
    ∀{vars : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
    YulTerm (BlockList vars vars b b')
| SeqCBlock  : 
    ∀ {vars : finset Identifier} (vars' : finset Identifier) 
      {vars'' : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
    YulTerm (CStatement vars vars' b b') -> 
    YulTerm (BlockList vars' vars'' b b') → 
    YulTerm (BlockList vars vars'' b b')

| NestedScope : 
    ∀ {vars : finset Identifier} (inner_vars inner_vars' : finset Identifier) 
      {b : IsInFor} {b' : IsInFunc}, 
    VarStore inner_vars → 
    YulTerm (BlockList (inner_vars ∪ vars) (inner_vars' ∪ vars) b b') → 
    YulTerm (CBlock vars b b')

| CCase : 
    ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc},
      Literal → YulTerm (CBlock vars b b') → YulTerm (SwitchBody vars b b') → 
      YulTerm (SwitchBody vars b b')
| CDefault : 
    ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc},
      YulTerm (CBlock vars b b') → YulTerm (SwitchBody vars b b')
| CNone : 
    ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc},
      YulTerm (SwitchBody vars b b')

| CFunctionCall : 
    ∀ {vars : finset Identifier} 
      (f_id : Identifier) (n : ℕ) {m : ℕ}, 
        (Γ f_id = some (n,m)) → 
        (fin n → YulTerm (CExpr vars 1)) →
        YulTerm (CExpr vars m)
| CId : 
    ∀ {vars : finset Identifier} (id : Identifier), 
    id ∈ vars → YulTerm (CExpr vars 1)
| CLit : 
    ∀ {vars : finset Identifier}, 
      Literal → YulTerm (CExpr vars 1)
| Scope : ∀ {vars_outer : finset Identifier} (vars_inner vars_fin : finset Identifier) 
               {n : ℕ} (ret_vars : vector Identifier n), 
    VarStore (vars_inner ∪ (tofinset' ret_vars)) →
    YulTerm (BlockList (vars_inner ∪ (tofinset' ret_vars)) (vars_fin ∪ (tofinset' ret_vars)) NotNestedInFor InFunc) → 
    YulTerm (CExpr vars_outer n)
| Result : 
    ∀ {vars : finset Identifier} {n : ℕ},
      vector Literal n → YulTerm (CExpr vars n)
    
| CBlock : 
  ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
    YulTerm (CBlock vars b b') → YulTerm (CStatement vars vars b b')
  -- Function definitions already parsed into FTContext.
| CVariableDeclarationAss : 
    ∀ {vars : finset Identifier} (n : ℕ) 
        (new_vars : fin n -> Identifier) {b : IsInFor} {b' : IsInFunc},
      YulTerm (CExpr vars n) → 
      YulTerm (CStatement vars (vars ∪ (tofinset new_vars)) b b')
| CVariableDeclaration : 
    ∀ {vars : finset Identifier} (n : ℕ) 
        (new_vars : fin n -> Identifier) {b : IsInFor} {b' : IsInFunc},
      YulTerm (CStatement vars (vars ∪ (tofinset new_vars)) b b')
| CAssignment :
    ∀ {vars : finset Identifier} (n : ℕ) 
        (ids : fin n -> Identifier) {b : IsInFor} {b' : IsInFunc},
      tofinset ids ⊆ vars → YulTerm (CExpr vars n) → 
      YulTerm (CStatement vars vars b b')
| CIf : 
    ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
      YulTerm (CExpr vars 1) → YulTerm (CBlock vars b b') → 
      YulTerm (CStatement vars vars b b')
| CExpressionStatement : 
    ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
    YulTerm (CExpr vars 0) -> YulTerm (CStatement vars vars b b')
| CSwitch : ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
    YulTerm (CExpr vars 1) → 
    YulTerm (SwitchBody vars b b') → 
    YulTerm (CStatement vars vars b b')
| CFor : 
  ∀ {vars : finset Identifier} (inner_vars inner_vars' inner_vars'' : finset Identifier)
      {b : IsInFor} {b' : IsInFunc},  
    YulTerm (BlockList vars (vars ∪ inner_vars) NotNestedInFor b') → 
    YulTerm (CExpr (vars ∪ inner_vars) 1) → 
    YulTerm (BlockList (vars ∪ inner_vars) (vars ∪ inner_vars') NestedInFor b') → 
    YulTerm (BlockList (vars ∪ inner_vars') (vars ∪ inner_vars'') NotNestedInFor b') → 
    YulTerm (CStatement vars vars b b')
| CBreak : 
    ∀ {vars : finset Identifier} {b' : IsInFunc}, 
      YulTerm (CStatement vars vars NestedInFor b')
| CContinue : 
    ∀ {vars : finset Identifier} {b' : IsInFunc}, 
      YulTerm (CStatement vars vars NestedInFor b')
| CLeave : 
    ∀ {vars : finset Identifier} {b : IsInFor}, 
      YulTerm (CStatement vars vars b InFunc)
| ForExecInit :
  ∀ {vars : finset Identifier} (curr_inner_vars inner_vars inner_vars' inner_vars'' : finset Identifier) 
      {b : IsInFor} {b' : IsInFunc}, 
    VarStore curr_inner_vars →
    YulTerm (CExpr (vars ∪ inner_vars) 1) → 
    YulTerm (BlockList (vars ∪ inner_vars) (vars ∪ inner_vars') NestedInFor b') → 
    YulTerm (BlockList (vars ∪ inner_vars') (vars ∪ inner_vars'') NotNestedInFor b') →
    YulTerm (BlockList (vars ∪ curr_inner_vars) (vars ∪ inner_vars) NotNestedInFor b') →
     YulTerm (CStatement vars vars b b')
| ForCheckCond : 
  ∀ {vars : finset Identifier} (inner_vars inner_vars' inner_vars'' : finset Identifier) 
      {b : IsInFor} {b' : IsInFunc}, 
    VarStore inner_vars →
    YulTerm (CExpr (vars ∪ inner_vars) 1) → 
    YulTerm (BlockList (vars ∪ inner_vars) (vars ∪ inner_vars') NestedInFor b') → 
    YulTerm (BlockList (vars ∪ inner_vars') (vars ∪ inner_vars'') NotNestedInFor b') →
    YulTerm (CExpr (vars ∪ inner_vars) 1) →
    YulTerm (CStatement vars vars b b')
| ForExecBody : 
  ∀ {vars : finset Identifier} (curr_inner_vars inner_vars inner_vars' inner_vars'' : finset Identifier) 
      {b : IsInFor} {b' : IsInFunc}, 
    VarStore curr_inner_vars →
    vars ∪ inner_vars ⊆ vars ∪ curr_inner_vars →
    YulTerm (CExpr (vars ∪ inner_vars) 1) → 
    YulTerm (BlockList (vars ∪ inner_vars) (vars ∪ inner_vars') NestedInFor b') → 
    YulTerm (BlockList (vars ∪ inner_vars') (vars ∪ inner_vars'') NotNestedInFor b') →
    YulTerm (BlockList (vars ∪ curr_inner_vars) (vars ∪ inner_vars') NestedInFor b') →
    YulTerm (CStatement vars vars b b')
| ForExecPost : 
  ∀ {vars : finset Identifier} (curr_inner_vars inner_vars inner_vars' inner_vars'' : finset Identifier) 
      {b : IsInFor} {b' : IsInFunc}, 
    VarStore curr_inner_vars →
    YulTerm (CExpr (vars ∪ inner_vars) 1) → 
    YulTerm (BlockList (vars ∪ inner_vars) (vars ∪ inner_vars') NestedInFor b') → 
    YulTerm (BlockList (vars ∪ inner_vars') (vars ∪ inner_vars'') NotNestedInFor b') →
    YulTerm (BlockList (vars ∪ curr_inner_vars) (vars ∪ inner_vars'') NotNestedInFor b') →
    YulTerm (CStatement vars vars b b')
| Skip : 
    ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
      YulTerm (CStatement vars vars b b')
  -- ForCheckCond, ForExecbody and Skip not in Yul specification, added for small step semantics.

open YulTerm

def getVariableUpdate : ∀ {t : TermType} , YulTerm Γ t → option (finset Identifier × finset Identifier)
| (BlockList vars vars' _ _) _ := some (vars, vars') 
| (CBlock _ _ _) _ := none
| (SwitchBody _ _ _) _ := none
| (CExpr _ _) _ := none
| (CStatement vars vars' _ _) _ := some (vars, vars')

lemma term_scope_monotonic : 
        ∀ {t : TermType} (term : YulTerm Γ t) (vars vars' : finset Identifier),
        getVariableUpdate Γ term = some (vars, vars') → vars ⊆ vars' :=
  begin
    intros ttype t,
    induction t,

    -- EmpCBlock
    intros vars vars' is_var_update i,
    intro i_in_vars,
    rw getVariableUpdate at is_var_update,
    injection is_var_update with is_var_update,
    injection is_var_update with vars_eq_tvars tvars_eq_tvars,
    rw [←tvars_eq_tvars, vars_eq_tvars],
    exact i_in_vars,

    -- SeqCBlock
    intros vars vars' is_var_update i,
    intro i_in_vars,
    rw getVariableUpdate at is_var_update,
    injection is_var_update with is_var_update,
    injection is_var_update with vars_eq_tvars tvars''_eq_vars',
    rw vars_eq_tvars at t_ᾰ,
    have int₁ := t_ih_ᾰ vars t_vars' _ i_in_vars,
    rw tvars''_eq_vars' at t_ᾰ_1,
    have int₂ := t_ih_ᾰ_1 t_vars' vars' _ int₁,
    exact int₂,
    rw getVariableUpdate,
    injection is_var_update with _ tvars''_eq_vars',
    rw tvars''_eq_vars',
    rw getVariableUpdate,
    rw vars_eq_tvars,

    -- Block, SwitchBody & Expr
    repeat {
      intros vars vars',
      intro f,
      rw getVariableUpdate at f,
      exfalso,
      exact option.some_ne_none (vars, vars') (eq.symm f),
    },

    -- CStatements that do not bring new variables into scope.
    repeat {
      intros vars vars',
      intro is_var_update,
      rw getVariableUpdate at is_var_update,
      injection is_var_update with is_var_update,
      injection is_var_update with vars_eq_tvars tvars_eq_vars',
      rw [←tvars_eq_vars', vars_eq_tvars],
      exact finset.subset.refl vars,
    },

    -- CVariableDeclaration, CVariableDeclarationAss
    repeat {
      intros vars vars',
      intro is_var_update,
      rw getVariableUpdate at is_var_update,
      injection is_var_update with is_var_update,
      injection is_var_update with vars_eq eq_vars',
      rw [←vars_eq,←eq_vars'],
      exact finset.subset_union_left _ _,
    },

  end      

def frame_TermType : TermType → finset Identifier → TermType
| (BlockList vars vars' b b') fvars := 
    BlockList (vars ∪ fvars) (vars' ∪ fvars) b b'
| (CBlock vars b b') fvars := CBlock (vars ∪ fvars) b b'
| (SwitchBody vars b b') fvars := SwitchBody (vars ∪ fvars) b b'
| (CExpr vars n) fvars := CExpr (vars ∪ fvars) n
| (CStatement vars vars' b b') fvars := 
    CStatement (vars ∪ fvars) (vars' ∪ fvars) b b'

lemma frame_lemma : 
  ∀ s₁ s₂ s₃ : finset Identifier, 
    s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  begin
    intros s₁ s₂ s₃,
    rw (finset.union_assoc s₁ s₂ s₃),
    rw (finset.union_assoc s₁ s₃ s₂),
    rw (finset.union_comm s₂ s₃),
  end

def frame : 
  ∀ {t : TermType} (fvars : finset Identifier), 
    YulTerm Γ t → YulTerm Γ (frame_TermType t fvars)
| (BlockList _ _ _ _) fvars EmpCBlock := EmpCBlock
| (BlockList _ _ _ _) fvars (SeqCBlock vars' cstmnt cblklst') :=
    SeqCBlock (vars' ∪ fvars) (frame fvars cstmnt) (frame fvars cblklst')
| (CBlock vars b b') fvars (NestedScope inner_vars inner_vars' σ blklst) :=
    let inner_vars_eq:= finset.union_assoc inner_vars vars fvars,
       inner_vars'_eq := finset.union_assoc inner_vars' vars fvars,
       cast (cblklst : YulTerm Γ (BlockList((inner_vars ∪ vars) ∪ fvars) ((inner_vars' ∪ vars) ∪ fvars) b b')) : 
                 YulTerm Γ (BlockList (inner_vars ∪ (vars ∪ fvars)) (inner_vars' ∪ (vars ∪ fvars)) b b') :=
              eq.rec (eq.rec cblklst inner_vars_eq) inner_vars'_eq
      in NestedScope inner_vars inner_vars' σ (cast $ frame fvars blklst)
| (SwitchBody _ _ _) fvars (CCase lit blk swtchbody) := 
    CCase lit (frame fvars blk) (frame fvars swtchbody)
| (SwitchBody _ _ _) fvars (CDefault blk) :=
    CDefault (frame fvars blk)
| (SwitchBody _ _ _) fvars CNone :=
    CNone
| (CExpr vars m) fvars (CFunctionCall f_id n p args) :=
    CFunctionCall f_id n p (λi, frame fvars (args i))
| (CExpr vars 1) fvars (CId i i_in_vars) :=
    CId i (finset.mem_of_subset (finset.subset_union_left vars fvars) i_in_vars)
| (CExpr _ 1) fvars (CLit lit) := CLit lit
| (CExpr _ _) fvars (Scope vars_inner vars_inner' ret_vars σ stmnt) :=
    Scope vars_inner vars_inner' ret_vars σ stmnt
| (CExpr _ _) fvars (Result res_vec) :=
    Result res_vec
| (CStatement _ _ _ _) fvars (CBlock blk) := 
    CBlock (frame fvars blk)
| (CStatement vars _ b b') fvars (CVariableDeclarationAss n new_vars cexpr) := 
    let cast (cstmnt : YulTerm Γ (CStatement (vars ∪ fvars) (vars ∪ fvars ∪ tofinset new_vars) b b'))
            : YulTerm Γ (CStatement (vars ∪ fvars) (vars ∪ tofinset new_vars ∪ fvars) b b') := 
              eq.rec cstmnt (finset.union_right_comm vars fvars (tofinset new_vars))
    in cast $ CVariableDeclarationAss n new_vars (frame fvars cexpr)
| (CStatement vars _ b b') fvars (CVariableDeclaration n new_vars) :=
    let cast (cstmnt : YulTerm Γ (CStatement (vars ∪ fvars) (vars ∪ fvars ∪ tofinset new_vars) b b'))
            : YulTerm Γ (CStatement (vars ∪ fvars) (vars ∪ tofinset new_vars ∪ fvars) b b') := 
              eq.rec cstmnt (finset.union_right_comm vars fvars (tofinset new_vars))
    in cast $ CVariableDeclaration n new_vars
| (CStatement vars _ b b') fvars (CAssignment n ids in_scope cexpr) :=
    CAssignment n ids
      (has_subset.subset.trans in_scope (finset.subset_union_left vars fvars)) 
      (frame fvars cexpr)
| (CStatement vars _ b b') fvars (CIf cexpr blk) :=
    CIf (frame fvars cexpr) (frame fvars blk)
| (CStatement vars _ b b') fvars (CExpressionStatement cexpr) :=
    CExpressionStatement (frame fvars cexpr)
| (CStatement vars _ b b') fvars (CSwitch cexpr swtchbody) :=
    CSwitch (frame fvars cexpr) (frame fvars swtchbody)
| (CStatement vars _ b b') fvars (CFor inner_vars inner_vars' inner_vars'' init cond body post) :=
    let init_framed : YulTerm Γ (BlockList (vars ∪ fvars) (vars ∪ fvars ∪ inner_vars) NotNestedInFor b') := 
          begin
            have init_framed := frame fvars init,
            rw frame_TermType at init_framed,
            apply eq.rec init_framed,
            rw frame_lemma,
          end,
        cond_framed : YulTerm Γ (CExpr (vars ∪ fvars ∪ inner_vars) 1) := 
          begin
            have cond_framed := frame fvars cond,
            rw frame_TermType at cond_framed,
            apply eq.rec cond_framed,
            rw frame_lemma,
          end,
        body_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars) (vars ∪ fvars ∪ inner_vars') NestedInFor b') :=
          begin
            have body_framed := frame fvars body,
            rw frame_TermType at body_framed,
            apply eq.rec body_framed,
            rw (frame_lemma vars inner_vars fvars),
            rw (frame_lemma vars inner_vars' fvars),
          end,
        post_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars') (vars ∪ fvars ∪ inner_vars'') NotNestedInFor b') := 
          begin
            have post_framed := frame fvars post,
            rw frame_TermType at post_framed,
            apply eq.rec post_framed,
            rw (frame_lemma vars inner_vars' fvars),
            rw (frame_lemma vars inner_vars'' fvars),
          end
    in CFor inner_vars inner_vars' inner_vars''
        init_framed cond_framed body_framed post_framed
| (CStatement vars _ b b') fvars CBreak := CBreak
| (CStatement vars _ b b') fvars CContinue := CContinue
| (CStatement vars _ b b') fvars CLeave := CLeave
| (CStatement vars _ b b') fvars 
      (ForExecInit curr_inner_vars inner_vars inner_vars' inner_vars'' σ cond loop post eval_init) :=
    let cond_framed : YulTerm Γ (CExpr (vars ∪ fvars ∪ inner_vars) 1) := 
          begin
            have cond_framed := frame fvars cond,
            rw frame_TermType at cond_framed,
            apply eq.rec cond_framed,
            rw frame_lemma,
          end,
        loop_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars) (vars ∪ fvars ∪ inner_vars') NestedInFor b') := 
          begin
            have loop_framed := frame fvars loop,
            rw frame_TermType at loop_framed,
            apply eq.rec loop_framed,
            rw (frame_lemma vars inner_vars fvars),
            rw (frame_lemma vars inner_vars' fvars),
          end,
        post_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars') (vars ∪ fvars ∪ inner_vars'') NotNestedInFor b') := 
          begin
            have post_framed := frame fvars post,
            rw frame_TermType at post_framed,
            apply eq.rec post_framed,
            rw (frame_lemma vars inner_vars' fvars),
            rw (frame_lemma vars inner_vars'' fvars),
          end,
        eval_init_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ curr_inner_vars) (vars ∪ fvars ∪ inner_vars) NotNestedInFor b') :=
          begin
            have eval_init_framed := frame fvars eval_init,
            rw frame_TermType at eval_init_framed,
            apply eq.rec eval_init_framed,
            rw (frame_lemma vars curr_inner_vars fvars),
            rw (frame_lemma vars inner_vars fvars),
          end
    in ForExecInit curr_inner_vars inner_vars inner_vars' inner_vars'' σ
        cond_framed loop_framed post_framed eval_init_framed
| (CStatement vars _ b b') fvars 
      (ForCheckCond inner_vars inner_vars' inner_vars'' σ cond loop post eval_cond) :=
    let cond_framed : YulTerm Γ (CExpr (vars ∪ fvars ∪ inner_vars) 1) := 
          begin
            have cond_framed := frame fvars cond,
            rw frame_TermType at cond_framed,
            apply eq.rec cond_framed,
            rw frame_lemma,
          end,
        loop_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars) (vars ∪ fvars ∪ inner_vars') NestedInFor b') := 
          begin
            have loop_framed := frame fvars loop,
            rw frame_TermType at loop_framed,
            apply eq.rec loop_framed,
            rw (frame_lemma vars inner_vars fvars),
            rw (frame_lemma vars inner_vars' fvars),
          end,
        post_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars') (vars ∪ fvars ∪ inner_vars'') NotNestedInFor b') := 
          begin
            have post_framed := frame fvars post,
            rw frame_TermType at post_framed,
            apply eq.rec post_framed,
            rw (frame_lemma vars inner_vars' fvars),
            rw (frame_lemma vars inner_vars'' fvars),
          end,
        eval_cond_framed : YulTerm Γ (CExpr (vars ∪ fvars ∪ inner_vars) 1) :=
          begin
            have eval_cond_framed := frame fvars eval_cond,
            rw frame_TermType at eval_cond_framed,
            apply eq.rec eval_cond_framed,
            rw (frame_lemma vars inner_vars fvars),
          end
    in ForCheckCond inner_vars inner_vars' inner_vars'' σ
        cond_framed loop_framed post_framed eval_cond_framed
| (CStatement vars _ b b') fvars 
      (ForExecBody curr_inner_vars inner_vars inner_vars' inner_vars'' σ p cond loop post eval_loop) :=
    let cond_framed : YulTerm Γ (CExpr (vars ∪ fvars ∪ inner_vars) 1) := 
          begin
            have cond_framed := frame fvars cond,
            rw frame_TermType at cond_framed,
            apply eq.rec cond_framed,
            rw frame_lemma,
          end,
        loop_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars) (vars ∪ fvars ∪ inner_vars') NestedInFor b') := 
          begin
            have loop_framed := frame fvars loop,
            rw frame_TermType at loop_framed,
            apply eq.rec loop_framed,
            rw (frame_lemma vars inner_vars fvars),
            rw (frame_lemma vars inner_vars' fvars),
          end,
        post_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars') (vars ∪ fvars ∪ inner_vars'') NotNestedInFor b') := 
          begin
            have post_framed := frame fvars post,
            rw frame_TermType at post_framed,
            apply eq.rec post_framed,
            rw (frame_lemma vars inner_vars' fvars),
            rw (frame_lemma vars inner_vars'' fvars),
          end,
        eval_loop_framed :YulTerm Γ (BlockList (vars ∪ fvars ∪ curr_inner_vars) (vars ∪ fvars ∪ inner_vars') NestedInFor b') :=
          begin
            have eval_loop_framed := frame fvars eval_loop,
            rw frame_TermType at eval_loop_framed,
            apply eq.rec eval_loop_framed,
            rw (frame_lemma vars inner_vars' fvars),
            rw (frame_lemma vars curr_inner_vars fvars),
          end,
        p' : vars ∪ fvars ∪ inner_vars ⊆ vars ∪ fvars ∪ curr_inner_vars :=
          begin
            intros i i_in,
            repeat {
              rw finset.mem_union at i_in,
            },
            repeat {
              rw finset.mem_union,
            },
            cases i_in with x y,
            exact or.inl x,
            cases finset.mem_union.1 (p (finset.mem_union_right vars y)) with h,
            exact or.inl (or.inl h),
            exact or.inr h,
          end
    in ForExecBody curr_inner_vars inner_vars inner_vars' inner_vars'' σ p'
        cond_framed loop_framed post_framed eval_loop_framed
| (CStatement vars _ b b') fvars 
      (ForExecPost curr_inner_vars inner_vars inner_vars' inner_vars'' σ cond loop post eval_post) :=
    let cond_framed : YulTerm Γ (CExpr (vars ∪ fvars ∪ inner_vars) 1) := 
          begin
            have cond_framed := frame fvars cond,
            rw frame_TermType at cond_framed,
            apply eq.rec cond_framed,
            rw frame_lemma,
          end,
        loop_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars) (vars ∪ fvars ∪ inner_vars') NestedInFor b') := 
          begin
            have loop_framed := frame fvars loop,
            rw frame_TermType at loop_framed,
            apply eq.rec loop_framed,
            rw (frame_lemma vars inner_vars fvars),
            rw (frame_lemma vars inner_vars' fvars),
          end,
        post_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ inner_vars') (vars ∪ fvars ∪ inner_vars'') NotNestedInFor b') := 
          begin
            have post_framed := frame fvars post,
            rw frame_TermType at post_framed,
            apply eq.rec post_framed,
            rw (frame_lemma vars inner_vars' fvars),
            rw (frame_lemma vars inner_vars'' fvars),
          end,
        eval_post_framed : YulTerm Γ (BlockList (vars ∪ fvars ∪ curr_inner_vars) (vars ∪ fvars ∪ inner_vars'') NotNestedInFor b') :=
          begin
            have eval_post_framed := frame fvars eval_post,
            rw frame_TermType at eval_post_framed,
            apply eq.rec eval_post_framed,
            rw (frame_lemma vars inner_vars'' fvars),
            rw (frame_lemma vars curr_inner_vars fvars),
          end
    in ForExecPost curr_inner_vars inner_vars inner_vars' inner_vars'' σ
        cond_framed loop_framed post_framed eval_post_framed
| (CStatement vars _ b b') fvars Skip := Skip 

def are_args_reduced : 
  ∀ {vars : finset Identifier} {n : ℕ}, 
    vector (YulTerm Γ (CExpr vars 1)) n → Prop
| _ 0 _ := true
| vars (nat.succ n) ⟨ (Result _) :: cexprs, p ⟩ := 
  are_args_reduced 
    (⟨ 
      cexprs, 
      by {
            rw list.length at p,
            exact (nat.add_right_cancel p),
          }
     ⟩ : vector (YulTerm Γ (CExpr vars 1)) n)
| _ (nat.succ n) ⟨ _ :: _, _ ⟩ := false

instance (vars : finset Identifier) (n : ℕ) 
  (cexprs : vector (YulTerm Γ (CExpr vars 1)) n) : 
    decidable (are_args_reduced Γ cexprs) :=
  begin
    induction n,
    rw are_args_reduced,
    apply decidable.is_true,
    trivial,
    cases cexprs,
    cases cexprs_val,
    exfalso,
    exact list.ne_nil_of_length_eq_succ cexprs_property (eq.refl list.nil),
    cases cexprs_val_hd,
    repeat {
      rw are_args_reduced,
      apply decidable.is_false,
      trivial,
    },
    rw are_args_reduced,
    exact n_ih ⟨ cexprs_val_tl, _ ⟩,
  end

lemma nil_reduced : 
  ∀ {Γ : FTContext} {vars : finset Identifier}, 
    @are_args_reduced Γ vars 0 vector.nil :=
  begin
    intros Γ vars,
    rw are_args_reduced,
    trivial,
  end 

def is_result : 
  ∀ {vars : finset Identifier} {n : ℕ}, 
    YulTerm Γ (CExpr vars n) -> Prop
| _ _ (Result _) := true
| _ _ (CLit _) := false
| _ _ (CId _ _) := false
| _ _ (CFunctionCall _ _ _ _) := false
| _ _ (Scope _ _ _ _ _) := false

instance 
  (vars : finset Identifier) (n : ℕ) 
    (cexpr : YulTerm Γ (CExpr vars n)) : decidable (is_result Γ cexpr) :=
  begin
    cases cexpr,
    repeat {
      rw is_result,
      apply decidable.is_false,
      trivial,
    },
    rw is_result,
    apply decidable.is_true,
    trivial,
  end

def is_skip : 
  ∀ {vars vars': finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
    YulTerm Γ (CStatement vars vars' b b') -> Prop
| _ _ _ _ Skip := true
| _ _ _ _ (CBlock _) := false
| _ _ _ _ (CVariableDeclarationAss _ _ _) := false
| _ _ _ _ (CVariableDeclaration _ _) := false
| _ _ _ _ (CAssignment _ _ _ _) := false
| _ _ _ _ (CIf _ _) := false
| _ _ _ _ (CExpressionStatement _) := false
| _ _ _ _ (CSwitch _ _) := false
| _ _ _ _ (CFor _ _ _ _ _ _ _) := false
| _ _ _ _ CBreak := false
| _ _ _ _ CContinue := false
| _ _ _ _ CLeave := false
| _ _ _ _ (ForExecInit _ _ _ _ _ _ _ _ _) := false
| _ _ _ _ (ForCheckCond _ _ _ _ _ _ _ _) := false
| _ _ _ _ (ForExecBody _ _ _ _ _ _ _ _ _ _) := false
| _ _ _ _ (ForExecPost _ _ _ _ _ _ _ _ _) := false

lemma is_skip_imp_vars_eq_vars' :
  ∀ {vars vars' : finset Identifier} {b : IsInFor} {b' : IsInFunc} 
      {cstmnt : YulTerm Γ (CStatement vars vars' b b')},
    is_skip Γ cstmnt → vars' = vars :=
  begin
    intros vars vars' b b' cstmnt cstmnt_is_skip,
    cases cstmnt,
    repeat {
      rw is_skip at cstmnt_is_skip,
    },
    repeat {
      exfalso,
      exact cstmnt_is_skip,
    },
  end

instance is_skip_decidable {vars vars' : finset Identifier} {b : IsInFor} {b' : IsInFunc}
  {stmnt : YulTerm Γ (CStatement vars vars' b b')} : decidable (is_skip Γ stmnt) :=
  begin
    cases stmnt,
    repeat{
      rw is_skip,
      apply decidable.is_false,
      trivial,
    },
    rw is_skip,
    apply decidable.is_true,
    trivial,
  end

def is_empcblock : 
  ∀ {vars vars' : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
    YulTerm Γ (BlockList vars vars' b b') → Prop 
| _ _ _ _ EmpCBlock := true
| _ _ _ _ _ := false

instance empcblock_decidable 
  {vars vars' : finset Identifier} {b : IsInFor} {b' : IsInFunc}
    {blklst : YulTerm Γ (BlockList vars vars' b b')} : 
  decidable (is_empcblock Γ blklst) :=
  begin
    cases blklst,
    rw is_empcblock,
    apply decidable.is_true,
    trivial,
    rw is_empcblock,
    apply decidable.is_false,
    trivial,
  end

lemma is_empcblock_imp_vars_eq_vars' : 
  ∀ {vars vars' : finset Identifier} {b : IsInFor} 
      {b' : IsInFunc} {cblk : YulTerm Γ (BlockList vars vars' b b')},
    is_empcblock Γ cblk → vars = vars' :=
  begin
    intros vars vars' b b' cblk cblk_is_empcblock,
    cases cblk,
    refl,
    exfalso,
    rw is_empcblock at cblk_is_empcblock,
    exact cblk_is_empcblock,
  end 



def is_empblock : 
  ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
    YulTerm Γ (CBlock vars b b') → Prop
| _ _ _ (NestedScope _ _ _ blklst) := is_empcblock Γ blklst

instance (vars : finset Identifier) (b : IsInFor) (b' : IsInFunc)
  (blk : YulTerm Γ (CBlock vars b b')) : decidable (is_empblock Γ blk) :=
  begin
    cases blk,
    rw is_empblock,
    exact YulCommands.empcblock_decidable Γ,
  end

def to_literal : ∀ {vars : finset Identifier} {n : ℕ}
      (cexpr : YulTerm Γ (CExpr vars n)), is_result Γ cexpr → vector Literal n
  | _ _ cexpr@(CFunctionCall _ _ _ _) cexpr_is_res := 
    let cexpr_n_is_res : ¬ is_result Γ cexpr :=
      begin
        rw is_result,
        intro f,
        exact f,
      end
    in absurd cexpr_is_res cexpr_n_is_res
  | _ _ cexpr@(CId _ _) cexpr_is_res := 
    let cexpr_n_is_res : ¬ is_result Γ cexpr :=
      begin
        rw is_result,
        intro f,
        exact f,
      end
    in absurd cexpr_is_res cexpr_n_is_res
  | _ _ cexpr@(CLit l) cexpr_is_res := 
    let cexpr_n_is_res : ¬ is_result Γ cexpr :=
      begin
        rw is_result,
        intro f,
        exact f,
      end
    in absurd cexpr_is_res cexpr_n_is_res
  | _ _ cexpr@(Scope _ _ _ _ _) cexpr_is_res := 
    let cexpr_n_is_res : ¬ is_result Γ cexpr :=
      begin
        rw is_result,
        intro f,
        exact f,
      end
    in absurd cexpr_is_res cexpr_n_is_res
  | _ _ cexpr@(Result res_vec) _ := res_vec

def getCase : 
  ∀ {vars : finset Identifier} {b : IsInFor} {b' : IsInFunc}, 
    Literal -> YulTerm Γ (SwitchBody vars b b') → YulTerm Γ (CBlock vars b b')
| _ _ _ _ CNone := NestedScope ∅ ∅ empStore EmpCBlock
| _ _ _ _ (CDefault blk) := blk
| _ _ _ l (CCase lit blk swtchbody') :=
  if l = lit 
  then blk
  else getCase l swtchbody'

lemma reduced_and_n_tail_reduced_imp_n_lit
  {vars : finset Identifier}
  (cexpr : YulTerm Γ (CExpr vars 1))
  {n : ℕ}
  (cexprs : vector (YulTerm Γ (CExpr vars 1)) n) :
    ¬ (are_args_reduced Γ (vector.cons cexpr cexprs)) → are_args_reduced Γ cexprs → 
      ¬ is_result Γ cexpr :=
  begin
    intros full_not_red tail_red,
    cases cexpr,
    repeat {
      rw is_result,
      intro f,
      exact f,
    },
    cases cexprs,
    exfalso,
    rw vector.cons at full_not_red,
    rw are_args_reduced at full_not_red,
    exact full_not_red(tail_red),
  end 

def get_lits : 
  ∀ {vars : finset Identifier} {n : ℕ} 
    (arg_cexprs : vector (YulTerm Γ (CExpr vars 1)) n),
  are_args_reduced Γ arg_cexprs → vector Literal n 
| _ 0 _ _ := vector.nil
| vars (nat.succ n) ⟨(Result lit) :: lit_cexprs, len_p⟩ p :=
  let lit_cexprs_vec' : vector (YulTerm Γ (CExpr vars 1)) n := 
        ⟨ lit_cexprs, 
          by {
            rw list.length at len_p,
            exact (nat.add_right_cancel len_p),
          }
        ⟩
  in vector.cons lit.head $ 
      get_lits lit_cexprs_vec' $
        by {
          rw are_args_reduced at p,
          exact p,
        }

end YulCommands