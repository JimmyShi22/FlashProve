-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/HeardAtReads.lean:
**heardNone_at_reads**: it pays the binder hh of k01_fifty_at9 (K01FiftyAt9.lean, this folder) in the
proof of k01_fifty_atBase (Johnson/Desc/K1/Law/K01FiftyAtBase.lean):
behind an accept of the sub-protocol at a link's reads (the commitment, then the step without a
round), from inside the promise in front, nothing is heard at the digits' seat: the field `heard` of
the state's parameters of the approximate range proof is `none` (`HeardNone`,
LookAtLater.lean). THE ONE PREMISE LEFT IS THE TOP's OWN BINDER O (the description, opened).
OBJECT: `blkL Z Bs.G₀ l false X arrs` (LaterOne.lean).
USER: the top of K01_law's fifty later places (its binder hh).
LETTERS: pol, lay, KL, F, Z, Bs, base₀, c, A, B (an opening's); Dm, dk, Mg₀; l, X, arrs; x, x', y.
HOW, by the sort of the link.
  a layers' link, the head's   the step without a round lays THE PLAN's parameters
                   (`tlHeard_layers`, `tlHeard_head`, QuietLook.lean); the plan is a member
                   of the public parameters Bs.G₀.W (`ProofFile.readsQuietAt`, `K8.ReadsQuiet.blockAt`), and
                   THE LOOKUPS' FILES' LAW IS CALLED: `First.Look.heardNoneAll_of_public`
                   (Johnson/Desc/First/Look/HeardNone.lean) at `IM.Open.public`
  an attention link   the step leaves the field (`tlHeard_att`), and so does the commitment
                   (`linkFresh_at_later`, PubAtLaterLook.lean); in front the promise holds the
                   public item linkFresh l, whose test's first clause is that very sentence
  `freshIn_mw`       [kernel] linkFresh l is open in front of each of the 25 reads' places.
                   `freshIn_fails`: the test can fail
  `heard_k1Quiet`    the step without a round, under `HeardNoneAll G.W`
  `LaterHeard B`, `laterHeard_k1Reads`
  `heardNone_at_reads_of`   the binder at a letter Mg₀ (hM: its list of extra public tests is empty),
                   under `HeardNoneAll Bs.G₀.W`
  `heardNone_at_reads`      **the binder, to the letter, at mgBase, from an opening**
The recursion limit is raised in this file (maxRecDepth 1000000), as in RestAtPlus13.lean: for
the elaboration of the kernel's evaluations alone.
What is not claimed. That a description can be opened. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RestAtPlus13
import Johnson.Desc.K1.Law.K01FiftyR
import Johnson.Desc.First.Look.HeardNone
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.First.Look (K3Data linkFreshC HeardNoneAll heardNoneAll_of_public)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll mgBase d13)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Keeps (Decides)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

variable {Cl : Type}

/-! ## 1 The step without a round behind the reads' commitment -/

/-- At a layers' link and at the head's: behind the step the field is the plan's. -/
theorem heard_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (hG : ∀ (g : ℕ) (hp : Layer.HPlan2), G[g]? = some hp → hp.tl.heard = none)
    (hH : H.tl.heard = none) (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) :
    Decides (fun _ s' : S => HeardNone s') q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, hg, rfl⟩ := Option.map_eq_some_iff.1 h
    intro s rs gs s' hd
    unfold HeardNone
    rw [tlHeard_layers hd]
    show hp.tl.heard.isNone = true
    rw [hG _ hp hg]
    rfl
  · split at h
    · obtain rfl := Option.some.inj h
      intro s rs gs s' hd
      unfold HeardNone
      rw [tlHeard_head hd]
      show H.tl.heard.isNone = true
      rw [hH]
      rfl
    · cases h

theorem readsQuietAt_heard {G : ProofFile.Ground} (hW : HeardNoneAll G.W) (l : Nat) (X : LinkH)
    (piece : Nat) (q : Block S Unit) (h : ProofFile.readsQuietAt G l X piece = some q) :
    Decides (fun s s' : S => HeardNone s → HeardNone s') q := by
  unfold ProofFile.readsQuietAt at h
  by_cases k1 : (X.kind == 1) = true
  · rw [if_pos k1] at h
    by_cases k2 : (piece == 4) = true
    · rw [if_pos k2] at h
      unfold First.Att.readsAtO at h
      obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
      intro s rs gs s' hd h0
      have hd' : First.Att.readsAtSO A s = .ok s' := hd
      unfold HeardNone at h0 ⊢
      rw [tlHeard_att hd']
      exact h0
    · rw [if_neg k2] at h
      cases h
  · rw [if_neg k1] at h
    by_cases k2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos k2] at h
      exact fun s rs gs s' hd _ => heard_blockAt hW.1 hW.2.2 h s rs gs s' hd
    · rw [if_neg k2] at h
      cases h

/-- **Nothing heard in front, nothing heard behind**, where the public parameters' plans have heard
nothing. -/
theorem heard_k1Quiet (G : ProofFile.Ground) (hW : HeardNoneAll G.W) (l : Nat) (X : LinkH) :
    Decides (fun s s' : S => HeardNone s → HeardNone s') (IM.k1Quiet G l X) := by
  unfold IM.k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact fun s rs gs s' h => nomatch h
  | some q => exact readsQuietAt_heard hW l X _ q hq

/-! ## 2 The commitment with the step joined behind it -/

/-- An accept of B on two rounds, from a state at which linkFresh's test holds: nothing is heard
behind. -/
def LaterHeard (B : Block S Cl) : Prop :=
  ∀ (d : K3Data) (m : Nat) (s s' : S) rs gs, rs.length = 2 → B.decide s rs gs = .ok s' →
    linkFreshC d m s = true → HeardNone s'

theorem laterHeard_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : Decides (fun s s' : S => HeardNone s → HeardNone s') q) :
    LaterHeard (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro d m s s' rs gs h2 h h0
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  have h1' : linkFreshC d m s₁ = true := by
    rw [linkFresh_at_later d m P link moment arrays s s₁ r₁ r₂ gs₁ h1]
    exact h0
  unfold linkFreshC at h1'
  simp only [Bool.and_eq_true] at h1'
  exact hq _ _ _ _ h3 h1'.1

theorem laterHeard_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (hW : HeardNoneAll G.W) (l : Nat)
    (X : LinkH) (pr : Nat) (reads : Option (List Nat)) :
    LaterHeard (IM.k1Reads Z G l X pr reads) :=
  laterHeard_joined _ _ _ _ _ _ (heard_k1Quiet G hW l X)

/-! ## 3 linkFresh l is open in front of the reads: the kernel's fact -/

theorem freshIn_mw : ((List.range 25).all fun l =>
    openB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)
      (.linkFresh l)) = true := by
  decide +kernel

/-- **The test can fail**: another link's item is not open there; link 3's own is not open in front
of the link's first sub-protocol, nor behind the lookup on the digits. -/
theorem freshIn_fails :
    openB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 false + 2)
      (.linkFresh 4) = false ∧
    openB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + 0 + 2) (.linkFresh 3) = false ∧
    openB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + 7 + 2) (.linkFresh 3) = false := by
  decide +kernel

/-! ## 4 The binder -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **The binder hh at a letter for the meaning beneath**, under the lookups' files' sentence on the
public parameters. -/
theorem heardNone_at_reads_of (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hW : HeardNoneAll Bs.G₀.W) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y,
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true) (noL l false) x y → HeardNone x'.2 := by
  intro l hl X arrs _ x x' y hy hIn
  have hin : Pub.linkFresh l ∈
      (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
        (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)) := by
    have e : (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more = mwMore :=
      plus13_more_closed Dm dk Mg₀ hM
    rw [e]
    exact open_of (List.all_eq_true.1 freshIn_mw l (List.mem_range.2 hl))
  have h0 : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub (.linkFresh l) x = true := inAt_pub hIn _ hin
  rw [pub_plus13, First.pubAll_linkFresh] at h0
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  exact laterHeard_k1Reads Z Bs.G₀ hW l X _ arrs Dm.pubD.d3 l x.2 x'.2 _ gs hlen hd h0

/-- **WHAT PAYS THE BINDER hh OF k01_fifty_at9 IN k01_fifty_atBase**, from the top's own opening. -/
theorem heardNone_at_reads {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base₀ : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open OnBytes.secondHashFunction pol lay KL F Z Bs base₀ c A B) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y,
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true) (noL l false) x y → HeardNone x'.2 :=
  heardNone_at_reads_of Dm dk mgBase rfl Z Bs (heardNoneAll_of_public O.public)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.freshIn_mw
#print axioms VerifiableInference.Desc.K1.freshIn_fails
#print axioms VerifiableInference.Desc.K1.heard_k1Quiet
#print axioms VerifiableInference.Desc.K1.heardNone_at_reads_of
#print axioms VerifiableInference.Desc.K1.heardNone_at_reads
