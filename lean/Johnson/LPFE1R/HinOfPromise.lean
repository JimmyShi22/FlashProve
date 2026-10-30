-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/HinOfPromise.lean: THE PREMISE hin OF hitems' THREE PAYERS
(Link/Law/HitemsJoin.lean: hitems_layers | hitems_attention; Link/Law/HitemsHead.lean:
hitems_head): "the table's public test formsIn says yes at each listed item, at every state of the
condition in front of the batching": IT IS IN THE TABLE's OWN PROMISE, AT EVERY ENTRY OF THE SORT's
ORDER OF CLAIMS BUT "K8.equations". Statements and proofs.

  formsIn_of_promise general in the data 𝔇, the lists and the border k: where the promise holds
                     without a mark, the item forms m kk r is open at k, e is one of the runs that
                     it stands for and e is not read ahead (𝔇.ah): K9.formsIn (𝔇.Rd m) (𝔇.N.group m)
                     e.1 e.2 says yes. By the promise's clause pubHeld (First/Borders.lean), the
                     tied public item formsIn, and what the composed meaning's test says at it
                     (mgAll_pub · pubAll_formsIn)
  named_full         BY THE KERNEL, on the written lists (the test: namedB): at each of the 25 links
                     every entry of the sort's order but "K8.equations" is a run of a forms item
                     that is open at the batching's border
  named_no           a control: behind the batching, which closes these items, the test says no at
                     every link
hin AT THE CLOSED CONSTANT (hin_at): LPFE1R/HinAtConst.lean, which calls these.

Limits. AT "K8.equations" NOTHING IS SAID: there the promise holds the weaker test formsInA (the run
is read ahead). The head is a premise. The full size alone. No soundness statement.

-/
import Johnson.P5J.K09List
import Johnson.Desc.First.PubAllAt
import Johnson.P5J.K10Open

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers start openSets pubOfItems
  pubHeld orderOf runsOf formsOf pubAll_formsIn)
open IM (subAt)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The public test at a run of an open item, out of the promise.** -/
theorem formsIn_of_promise {A : Type} {F : Frame} (links : List ModelPart) (ps : List Place)
    (get : A → P × S) (k : ℕ) (a : A × F.E.Str)
    (hon : onQ 𝔇.N (mgAll 𝔇 Mg) links ps get k a) (hm : (get a.1).2.failed = none)
    {m kk : ℕ} {r : String}
    (hO : Item.forms m kk r ∈ (openSets links ps (start links))[k]?.getD [])
    {e : ℕ × String} (he : e ∈ 𝔇.runs m kk r) (hah : 𝔇.ah e.1 e.2 = false) :
    K9.formsIn (𝔇.Rd m) (𝔇.N.group m) e.1 e.2 (get a.1).2 = true := by
  rcases hon.2 with hx | ⟨hb, -, -, -⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at hb
    have hp := hb.1.2
    unfold pubHeld at hp
    have hq : Pub.formsIn m kk r ∈ pubOfItems ((openSets links ps (start links))[k]?.getD []) :=
      List.mem_flatMap.2 ⟨_, hO, List.mem_singleton.2 rfl⟩
    have h1 := List.all_eq_true.1 hp _ (List.mem_append_right _ hq)
    rw [mgAll_pub, pubAll_formsIn] at h1
    have h2 := List.all_eq_true.1 h1 e he
    have ea : 𝔇.pubD.ah e.1 e.2 = false := hah
    rw [ea] at h2
    simpa using h2

end

/-- Every entry of link m's sort's order but "K8.equations" is a run of a forms item of link m that
is open at border k. -/
def namedB (k m : ℕ) : Bool :=
  (orderOf (subAt m)).all fun e => e.2 == "K8.equations" ||
    (P5J.oAt k).any fun i => match i with
      | .forms m' kk r => m' == m && (runsOf (subAt m) kk r).contains e
      | _ => false

set_option maxRecDepth 1000000 in
theorem named_full : ((List.range 25).all fun m =>
    namedB (batchAt P5J.fullLinks P5J.At.ps m) m) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: behind the batching, which closes these items, the test says no at every link. -/
theorem named_no : ((List.range 25).any fun m =>
    namedB (batchAt P5J.fullLinks P5J.At.ps m + 1) m) = false := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.formsIn_of_promise
#print axioms VerifiableInference.Desc.LinkJoin.named_full
#print axioms VerifiableInference.Desc.LinkJoin.named_no
