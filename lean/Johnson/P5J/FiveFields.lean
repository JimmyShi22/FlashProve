-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/FiveFields.lean: THE TOWER's FIVE ROWS THAT ARE LAWS (FiveF, Johnson/P5J/TowerEnd.lean),
AT THE COMPOSED MEANING's CLOSED CONSTANT (AtMgA.Five, Johnson/P5J/RowsAtAll.lean), EACH FIELD UNDER
A NAME OF ITS OWN. IT IMPORTS ThirdParty/. Five definitions, one equivalence.

Why. h.Five 𝔏 n is one structure of five fields whose types are long terms in the tower's local
notations. A file that pays one field wants to end in that field's own type, and a join wants to
keep a field that is not paid yet BY NAME. The five definitions here are these types, NAMED
THROUGH THE STRUCTURE's OWN PROJECTIONS (rowTypeAt fun V => FiveF.‹field› V: Lean fills the type
in): nothing is typed anew, and a lemma that ends in "fieldOf (fun V =>
FiveF.‹field› V)" ends in these by unfolding. five_iff: THE CHECK, BY LEAN: the structure is just
the conjunction of the five.

  h.HeadCutsF 𝔏 n · h.ReplyLeavesF 𝔏 n · h.SharedJointF 𝔏 n · h.Leads3F 𝔏 n · h.TablesFitF 𝔏 n
  AtMgA.five_iff    h.Five 𝔏 n ↔ the five together
  AtMgA.five_mk     the maker, from the five

Limits. Names and an unfolding: no field is paid. No soundness statement.
-/
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

/-- The type of a structure's field, named through its projection (as
Desc.K14.Law.fieldOf, Johnson/Desc/K14/Law/LedgerAtFree.lean: the same text under a name of this
namespace, so that this file imports the tower alone; NOT the name P5J.fieldAt, which
Johnson/P5J/LeftOfParts.lean declares for the same text). -/
abbrev rowTypeAt {A T : Prop} (_ : A → T) : Prop := T

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The head's four parts together give the head's half in plain integers. -/
def AtMgA.HeadCutsF (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (n : ℕ) : Prop := rowTypeAt fun V : h.Five 𝔏 n => FiveF.head_cuts V

/-- Every piece leaves the heard reply, but where the table lays the token. -/
def AtMgA.ReplyLeavesF (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (n : ℕ) : Prop :=
  rowTypeAt fun V : h.Five 𝔏 n => FiveF.reply_leaves V

/-- The shared chain's pieces' laws, the slots behind one key. -/
def AtMgA.SharedJointF (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (n : ℕ) : Prop :=
  rowTypeAt fun V : h.Five 𝔏 n => FiveF.shared_joint_count V

/-- The last chain's pieces, at its table. -/
def AtMgA.Leads3F (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (n : ℕ) : Prop := rowTypeAt fun V : h.Five 𝔏 n => FiveF.leads3_last_chains_table V

/-- The three tables fit the starts and each other. -/
def AtMgA.TablesFitF (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (n : ℕ) : Prop :=
  rowTypeAt fun V : h.Five 𝔏 n => FiveF.tables_fit V

/-- **The maker.** -/
theorem AtMgA.five_mk (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (n : ℕ) (a : h.HeadCutsF 𝔏 n) (b : h.ReplyLeavesF 𝔏 n) (c : h.SharedJointF 𝔏 n)
    (d : h.Leads3F 𝔏 n) (e : h.TablesFitF 𝔏 n) : h.Five 𝔏 n :=
  FiveF.mk a b c d e

/-- **The structure is just the five together.** -/
theorem AtMgA.five_iff (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (n : ℕ) :
    h.Five 𝔏 n ↔ h.HeadCutsF 𝔏 n ∧ h.ReplyLeavesF 𝔏 n ∧ h.SharedJointF 𝔏 n ∧ h.Leads3F 𝔏 n ∧
      h.TablesFitF 𝔏 n :=
  ⟨fun V => ⟨FiveF.head_cuts V, FiveF.reply_leaves V, FiveF.shared_joint_count V,
      FiveF.leads3_last_chains_table V, FiveF.tables_fit V⟩,
    fun V => h.five_mk 𝔏 n V.1 V.2.1 V.2.2.1 V.2.2.2.1 V.2.2.2.2⟩

end P5J

#print axioms P5J.AtMgA.five_mk
#print axioms P5J.AtMgA.five_iff
