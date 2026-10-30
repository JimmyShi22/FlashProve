-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/K12LawR.lean:
THE LAW OF THE PROXIMITY
TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN, AS A STATEMENT: the kind's share of the chain
of promises in the form with a condition that every accepting step hands on: KindTiedR (TiedR.lean)
at the kind K12 and the table's written lists. DEFINITIONS, AND WHERE THE KIND STANDS. THE LAW
ITSELF IS PROVED NOWHERE: it is meant as a hypothesis of a theorem that joins the kinds' laws.

  k12AllB, k12AllB_full   a test over a list of places, decided by the kernel at the written list
                    flatPlacesOf linksFull true (Johnson/Desc/Sound/AtDriver.lean)
  k12AllB_nil, k12AllB_twice   the test can fail: at the empty list; at the written list with a
                    second place of the kind at its end
  k12_at_354        number 354 of the written list is the place ⟨1, none, 2, K12⟩: SO THE SHARE IS
                    NOT HAD FOR NOTHING for want of a place; but where l has no piece at 354 it is
                    had for nothing: the l of whoever joins the kinds must have one
  k12_places_full   the kind stands there and nowhere else in that list
  k12_at_of, k12_places_of, kindTiedR_k12_iff   the same three at any lists at which the test passes
  K12LawR N Mg Rch E l   THE STATEMENT: KindTiedR N Mg linksFull (flatPlacesOf linksFull true) Rch E
                    l K12: general in the table's numbers N, its meaning Mg, the condition Rch, the
                    extractors E and the list of pieces l: whoever joins the kinds lays its own
  k12LawR_iff       it is ONE tie at ONE number: TiedAtR (Johnson/Desc/Sound/ChainOfPromisesR.lean)
                    at 354, of the piece that stands there
  LastTypedAt o pol lay KL   the one named condition under which K12's files' theorems at this seat
                    stand: at what ProofFile.pubPlain returns at the three files, the sized stages of the
                    first chain's last test are the typed list szLFull. To the letter the body of
                    LastIsTyped (H2K12/ChainAtLast.lean) at a VerifierAndGoals.PublicFiles's three files; written out
                    here: so this file does not import that one
  K12LawCounted     LastTypedAt → K12LawR

WHETHER K12LawR CAN BE MET IS SHOWN NOWHERE. It has no premise of its own, so it is not idle by a
premise that fails; but if it is false at the letters at which it is called, whatever is proved from
it says nothing. Rch IS A PARAMETER OF THE DEFINITION, bound by no "for all": AT WHICH Rch IT IS
CALLED IS THE CALLER's CHOICE: it is meant at the one condition "reached" picked for every kind. At
Rch := fun _ _ => True it asks the five ties at every state that meets the table's promise, and is
very likely false: K12's files' road at 354 spends facts that hold of reached states alone. WHAT
LIES TOWARDS IT, AND WHAT DOES NOT:
(a) The facts on codes are no open condition here. codes_of_johOk
(Johnson/Desc/K12/Law/CodesJoh.lean) gives them at the library's Johnson letters from a test with
code, in CodesJoh.lean's head's words "with the theorem on codes laid in (Cb.Gl.bchks46At,
Cb/Bridge/GlCodesProved.lean)", and, from the same head: "The theorem on codes rests on the files
under ThirdParty/, adapted from ArkLib and Mathlib
(lean/LIMITS.md, L15)."
(b) At the file's own piece at this seat, where the family of errors is the cap, the piece's
reduction leads to the game's conclusion (GameFirstCap: game_at_Last, H2K12/TileAtLast.lean),
under LastIsTyped, the goals' scope, ProofFile.onlineDescription's return and two tests. In scope, at secondHashFunction, that
premise follows from a yes of the verifier's own gate: lastTypedAt_of_live (LastTypedOfLaid.lean).
(c) THE ROAD FROM THAT GAME TO TiedAtR IS UNWRITTEN: the game ends at "nothing promised" and at a
relation of K12's files' own; TiedAtR asks GoodIn at four letters and five ties to the table's
promise, relations and meanings, "a mark stays" and "decodes rides". Of these one is plain: no
accepting step starts at a marked state (enterFinish, Johnson/Desc/K12/AtFinish.lean).
THE KIND's THREE OTHER PLACES (numbers 9 and 10 of the shared chain, number 2 of the last chain) ARE
NOT SPOKEN OF: KindTiedR is of the first chain's table alone; the files that compose the two other
tables take the kind there in their own forms.
Limits. No soundness statement. Nothing on hiding. k12AllB_full is decided at one version of the
written lists; at another it would have to be decided again.

-/
import Johnson.Desc.Sound.TiedR
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart
import Johnson.Desc.K12.Law.Sizes.StagesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (KindName Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start flatPlacesOf)

/-- The test over a list of places: the kind K12 stands at number 354, as the place
⟨1, none, 2, K12⟩, and nowhere else. -/
def k12AllB (ps : List Place) : Bool :=
  (ps[354]? == some ⟨1, none, 2, .K12⟩) &&
    (List.range ps.length).all fun i => i == 354 || ((ps[i]?).map (·.kind)) != some .K12

/-- By the kernel, at the written list. -/
theorem k12AllB_full : k12AllB (flatPlacesOf linksFull true) = true := by decide +kernel

/-- The test can fail: at the empty list. -/
theorem k12AllB_nil : k12AllB [] = false := by decide +kernel

/-- The test can fail: at the written list with a second place of the kind laid at its end. -/
theorem k12AllB_twice :
    k12AllB (flatPlacesOf linksFull true ++ [⟨1, none, 2, .K12⟩]) = false := by decide +kernel

/-- Where the test passes, the kind has a place in the list. -/
theorem k12_at_of {ps : List Place} (h : k12AllB ps = true) :
    ps[354]? = some ⟨1, none, 2, .K12⟩ := by
  unfold k12AllB at h
  rw [Bool.and_eq_true] at h
  exact beq_iff_eq.1 h.1

/-- And no other. -/
theorem k12_places_of {ps : List Place} (h : k12AllB ps = true) (i : ℕ) (a : Place)
    (ha : ps[i]? = some a) (hk : a.kind = .K12) : i = 354 ∧ a = ⟨1, none, 2, .K12⟩ := by
  have h0 := k12_at_of h
  unfold k12AllB at h
  rw [Bool.and_eq_true] at h
  have hi : i < ps.length := (List.getElem?_eq_some_iff.1 ha).1
  have h2 := List.all_eq_true.1 h.2 i (List.mem_range.2 hi)
  have e : i = 354 := by
    rcases Bool.or_eq_true_iff.1 h2 with h3 | h3
    · exact beq_iff_eq.1 h3
    · rw [ha] at h3
      simp [hk] at h3
  subst e
  exact ⟨rfl, Option.some.inj (ha.symm.trans h0)⟩

/-- **The kind has a place in the written list.** -/
theorem k12_at_354 : (flatPlacesOf linksFull true)[354]? = some ⟨1, none, 2, .K12⟩ :=
  k12_at_of k12AllB_full

/-- **And no other.** -/
theorem k12_places_full (i : ℕ) (a : Place) (ha : (flatPlacesOf linksFull true)[i]? = some a)
    (hk : a.kind = .K12) : i = 354 ∧ a = ⟨1, none, 2, .K12⟩ :=
  k12_places_of k12AllB_full i a ha hk

section
variable {Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
  (E : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str →
    (P × VerifiableInference.Desc.First.S) × Fr.E.Str → W → W)
  (l : List (Piece C Fr (P × VerifiableInference.Desc.First.S) Cl W))

/-- At any two lists of the table at which the test passes, the kind's share is one tie at one
number. -/
theorem kindTiedR_k12_iff (links : List ModelPart) {ps : List Place} (h : k12AllB ps = true) :
    KindTiedR N Mg links ps Rch E l KindName.K12 ↔ ∀ q, l[354]? = some q →
      TiedAtR N Mg links ps (fun a => a) Rch 354 (q.withMap (E 354)) := by
  constructor
  · intro H q hq
    exact H 354 q _ hq (k12_at_of h) rfl
  · intro H i q a hq ha hk
    obtain ⟨rfl, -⟩ := k12_places_of h i a ha hk
    exact H q hq

/-- **The kind K12's share of the chain of promises on the first chain.** Whether it
can be met is shown nowhere. -/
def K12LawR : Prop :=
  KindTiedR N Mg linksFull (flatPlacesOf linksFull true) Rch E l KindName.K12

/-- It is one tie at one number. -/
theorem k12LawR_iff : K12LawR N Mg Rch E l ↔ ∀ q, l[354]? = some q →
    TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 354
      (q.withMap (E 354)) :=
  kindTiedR_k12_iff N Mg Rch E l linksFull k12AllB_full

/-- The named condition of K12's files' theorems at this seat: the sized stages of the first chain's
last test are the typed list. -/
def LastTypedAt (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) : Prop :=
  ∀ Z, ProofFile.pubPlain o pol lay KL = .ok Z →
    Z.made.p.chains.made.sized.proof.last.stages = H2K.Member.szLFull

/-- **The law under that condition.** -/
def K12LawCounted (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) : Prop :=
  LastTypedAt o pol lay KL → K12LawR N Mg Rch E l

theorem K12LawR.counted (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (h : K12LawR N Mg Rch E l) :
    K12LawCounted N Mg Rch E l o pol lay KL := fun _ => h
end

end H2K12

#print axioms H2K12.k12AllB_full
#print axioms H2K12.k12AllB_twice
#print axioms H2K12.k12_places_full
#print axioms H2K12.kindTiedR_k12_iff
#print axioms H2K12.k12LawR_iff
