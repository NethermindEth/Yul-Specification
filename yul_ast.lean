
/- Yul specification:
   https://docs.soliditylang.org/en/v0.8.9/yul.html
 -/

import data.fin.basic

def UInt256_max : ℕ := 2^256 
def UInt256 := fin UInt256_max
def Literal := UInt256
def Identifier := string

lemma zero_lt_uint256_max : 0 < UInt256_max :=
  begin
    cases (nat.eq_zero_or_pos UInt256_max),
    exfalso,
    injection h,
  end 

def literal_zero : Literal :=
  fin.mk 0 zero_lt_uint256_max

/- 
  Types representing Expressions and Statements
  from the Yul specification. In contrast to the
  Yul specification, they are mutually recursive.
  This is to permit partial evaluated lexical scopes,
  so is needed to give a small step semantics for Yul.
-/

-- mutual inductive Expr, Statement
-- with Expr : Type
--   | FunctionCall : Identifier → list Expr → Expr
--   | Id : Identifier → Expr
--   | Lit : Literal → Expr
-- with Statement : Type
--   | Block : list Statement → Statement
--   | FunctionDefinition : Identifier → list Identifier → list Identifier → Statement → Statement
--   | VariableDeclaration : list Identifier → Expr → Statement
--   | Assignment : list Identifier → Expr → Statement
--   | If : Expr → list Statement → Statement
--   | ExpressionStatement : Expr -> Statement
--   | Switch : Expr → ((list (Literal × Statement)) × Statement) → Statement
--   | For : list Statement → Expr → list Statement → list Statement → Statement
--   | Break : Statement
--   | Continue : Statement 
--   | Leave : Statement