-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/BridgeKind.lean: ONE KIND's SHARE OF THE CHAIN OF PROMISES (`KindTied`,
Johnson/Desc/Sound/TiedPlaces.lean), TYPED AT THE WIDER FILLING `plus13 D d Mg`,
GIVES THAT KIND's SHARE IN THE SECOND FORM AT Mg: a tie `TiedAtR` at every place of the kind. A
definition, and one statement with its proof; free of the kind.
  `doorsFitAllB M₀ M cA links ps`: the test on the two doors (`doorsFitB`) at every border of the
  list. `kind_plus13`: from `KindTied N (plus13 D d Mg) links ps E l K`: WHERE that test accepts;
  the condition Rch gives `FactsK13` at every state without a mark; and Rch is handed on over each
    piece of the list.
The end is written out (∀ i q a, … → `TiedAtR` …): it is `KindTied`'s text with `TiedAtR` in
`TiedAt`'s place. What is not claimed. The premises. Nothing on soundness. Terms:
lean/GLOSSARY.md.
-/
import Johnson.Desc.K13.Law.BridgeK13
import Johnson.Desc.Sound.TiedPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers More)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Sound (Frame Piece TiedAtR HandsOn KindTied doorsFitB)

/-- The test on the two doors at every border of the list. -/
def doorsFitAllB (M₀ M : More) (cA : Pub → Bool) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range (ps.length + 1)).all fun k => doorsFitB M₀ M cA links ps k

/-- **One kind's share, carried.** -/
theorem kind_plus13 {Pp W Cl : Type} {nR : ℕ} {C : CK} {Fr : Frame} (D : DataK13 Pp W nR)
    (d : K12Data) (Mg : Meaning Pp W) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (E : ℕ → (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → W → W)
    (l : List (Piece C Fr (Pp × S) Cl W)) (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (K : KindName)
    (hD : doorsFitAllB Mg.more (plus13 D d Mg).more cA13 links ps = true)
    (hF : ∀ j a, Rch j a → a.1.2.failed = none → FactsK13 D d Mg a.1)
    (hs : ∀ i q, l[i]? = some q → HandsOn Rch i (q.withMap (E i)))
    (h : KindTied N (plus13 D d Mg) links ps E l K) :
    ∀ i q a, l[i]? = some q → ps[i]? = some a → a.kind = K →
      TiedAtR N Mg links ps (fun a => a) Rch i (q.withMap (E i)) := by
  intro i q a hq ha hk
  have hi : i < ps.length := (List.getElem?_eq_some_iff.1 ha).1
  have hall := List.all_eq_true.1 hD
  exact tiedAtR_plus13 D d Mg N links ps (fun a => a) Rch i _
    (hall i (List.mem_range.2 (by omega))) (hall (i + 1) (List.mem_range.2 (by omega))) hF
    (hs i q hq) (h i q a hq ha hk)

end VerifiableInference.Desc.K13.Law
