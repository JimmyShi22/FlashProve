-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K3Seat.lean.
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K3's blocks (the lookups on the calls and
on the digits) at their places in
onlineDescription's first chain.
OBJECT. THE SEATED CONSTANT: VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt X) X Z.first.codes Z.first.shape a (Johnson/Desc/First/Look/K3Stated.lean · Johnson/Desc/ProofFile/Lot/K3.lean),
at the driver's own address a, as it stands at F.first.links[l].hear[1] | hear[6] (the head's link 24: hear[2] | hear[7]), l < 25.
USER. The lookups' laws at the made block; the run «planes», stated by this block at its readers; the rows on the tables.
LETTERS. As in Johnson/IMR/K6Seat.lean; b': HANDED OUT BY theStated … a = some b', every argument a
term of X, Z and l.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

  lookAt_link       lookAt's place bears the link's number.
  theOwn_place | theStated_place   the block that K3.theOwn | theStated makes at an address stands at that address.
  k3Hear_mem        a block b' of K3's lot is theStated … b'.place = some b'.
  k3_alone          at an opening's letters, at every link l and index i (2 ≤ i + 1 ≤ 9) at which kindsBeforeBatching has K3: the chain's block there IS seatedAs sameReply b' b.name a, a := ⟨1, some l, i + 1, K3⟩, with
                    theStated … a = some b'. No premise on scope.
  k3_of             in scope, for every l < 25: both lookups.
  k3_alone_z        the same in one piece, from onlineDescription's value.
  k3_yes            yes_alone at K3's addresses.

WHERE THE PREMISES COME FROM: as in K6Seat.lean: that onlineDescription returns in scope is a premise.
What is not claimed. Nothing on what theStated's block is made of (lookAt's place, the quiet step that the kind itself joins behind, the readers): that is the lookup's files' text. No soundness.
-/
import Johnson.IMR.LaidFirst
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.Look (lookAt placeAt)
open ProofFile (Cl)

/-- lookAt's place bears the link's number. -/
theorem lookAt_link {X : Verify.Public} {i : ℕ} {digits : Bool}
    {x : VerifiableInference.Desc.First.Look.Place} (h : lookAt X i digits = some x) :
    x.link = i := by
  unfold lookAt at h
  dsimp only at h
  generalize (if X.p4 = true then 2 else 1) = step at h
  split at h
  · split at h
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
      rfl
    · obtain rfl := Option.some.inj h
      rfl
  · split at h
    · obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        rfl
      · obtain rfl := Option.some.inj h
        rfl
    · obtain ⟨a, _, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        rfl
      · obtain rfl := Option.some.inj h
        rfl

section
variable {C : Type} {claim : Aff → C} {X : Verify.Public} {codes : Codes} {shape : Params.ReqShape}
  {a : Place}

/-- **The block that K3.theOwn makes at an address stands at that address.** -/
theorem theOwn_place {runs : Bool} {c : Block S C}
    (h : VerifiableInference.Desc.K3.theOwn claim runs X codes shape a = some c) : c.place = a := by
  unfold VerifiableInference.Desc.K3.theOwn at h
  split at h
  · cases h
  · rename_i hca
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨dg, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · obtain ⟨p, h1, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      unfold placeAt at h1
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h1
      have hc : a.chain = 1 ∧ a.kind = KindName.K3 := by simpa using hca
      have e : (⟨1, some x.link, a.piece, KindName.K3⟩ : Place) = a := by
        obtain ⟨ch, lk, pc, kd⟩ := a
        obtain ⟨rfl, rfl⟩ := hc
        obtain rfl : lk = some i := hi
        rw [lookAt_link hx]
      dsimp only
      split <;> exact e

theorem theStated_place {readers : ℕ → Option (VerifiableInference.Desc.K3.Readers S)} {b : Block S C}
    (h : VerifiableInference.Desc.K3.theStated claim readers X codes shape a = some b) :
    b.place = a := by
  unfold VerifiableInference.Desc.K3.theStated at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  have hk : w.place = a := by
    unfold VerifiableInference.Desc.K3.theWhole at hw
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hw
    have := theOwn_place hc
    split <;> exact this
  split at h
  · obtain rfl := Option.some.inj h
    exact hk
  · split at h
    · obtain rfl := Option.some.inj h
      exact hk
    · split at h
      · obtain rfl := Option.some.inj h
        exact hk
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact hk

end

/-- K3's files' block (K3.theStated) at an address, at the lot's own letters. -/
abbrev k3At (X : Verify.Public) (Z : ProofFile.Pub) (a : Place) : Option (Block S Cl) :=
  VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt X) X Z.first.codes
    Z.first.shape a

/-- A block of K3's lot is the kind's own at the block's own place. -/
theorem k3Hear_mem {Z : ProofFile.Pub} {b' : Block S Cl} (h : b' ∈ K3Lot.hear Z) :
    k3At Z.p.X Z b'.place = some b' := by
  unfold K3Lot.hear at h
  obtain ⟨x, _, h⟩ := List.mem_filterMap.1 h
  have e := theStated_place h
  rw [e]
  exact h

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The chain's block at a place of kind K3 is the kind's own at that address, alone.** -/
theorem k3_alone (O : Open o pol lay KL F Z Bs base c A B) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K3) (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk b b', c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧
      k3At Bs.G₀.W Z { chain := 1, link := some l, piece := i + 1, kind := .K3 } = some b' ∧
      LaidAlone ProofFile.sameReply b b' b.name { chain := 1, link := some l, piece := i + 1, kind := .K3 } := by
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    chain_hear_alone O.made O.places O.chain l sub hl i .K3 hk (by decide) (by decide) hi
  obtain rfl : L = K3Lot.lot Z := lot_of_kind hL hb' (by rw [ep]; rfl)
  have hb'' : b' ∈ K3Lot.hear Z := by
    rcases blocks_mem hb' with ⟨y, hy, -⟩ | h
    · exact nomatch hy
    · exact h
  have hat := k3Hear_mem hb''
  rw [ep, ← O.W] at hat
  refine ⟨Lk, b, b', e1, e2, hat, ?_⟩
  rw [alone_name hla]
  exact hla

end

/-- The index of the lookup on the calls | on the digits in link l. -/
abbrev k3Ix (l : ℕ) (digits : Bool) : ℕ := (if digits then 6 else 1) + (if l = 24 then 1 else 0)

/-- K3's address. -/
abbrev k3Place (l : ℕ) (digits : Bool) : Place :=
  { chain := 1, link := some l, piece := k3Ix l digits + 1, kind := .K3 }

/-- **BOTH LOOKUPS, AT ALL 25 LINKS: THE KIND's OWN BLOCK AT THE DRIVER's ADDRESS, ALONE.** -/
theorem k3_of {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∀ digits : Bool, ∃ (Lk : Link S Cl) (b b' : Block S Cl),
      c.links[l]? = some Lk ∧ Lk.hear[k3Ix l digits]? = some b ∧
      k3At Bs.G₀.W Z (k3Place l digits) = some b' ∧
      LaidAlone ProofFile.sameReply b b' b.name (k3Place l digits) := by
  intro l hl digits
  have hZ := O.pub
  have hG := O.blank
  by_cases h24 : l = 24
  · subst h24
    have hk : (kindsBeforeBatching .head (24 == 0))[k3Ix 24 digits]? = some KindName.K3 := by
      unfold kindsBeforeBatching
      cases digits <;> rfl
    exact k3_alone O 24 .head (subs_head hS hR hZ hG) (k3Ix 24 digits) hk (by cases digits <;> decide)
  · have hix : k3Ix l digits = if digits then 6 else 1 := by
      show (if digits then 6 else 1) + (if l = 24 then 1 else 0) = _
      rw [if_neg h24]
      rfl
    have hpl : k3Place l digits =
        { chain := 1, link := some l, piece := (if digits then 6 else 1) + 1, kind := .K3 } := by
      show ({ chain := 1, link := some l, piece := k3Ix l digits + 1, kind := .K3 } : Place) = _
      rw [hix]
    rw [hix, hpl]
    by_cases he : l % 2 = 0
    · have ej : 2 * (l / 2) = l := by omega
      have hsub := subs_at hS hR hZ hG (g := l / 2) (by omega)
      rw [ej] at hsub
      have hk : (kindsBeforeBatching .layers (l == 0))[if digits then 6 else 1]? = some KindName.K3 := by
        unfold kindsBeforeBatching
        cases digits <;> rfl
      exact k3_alone O l .layers hsub _ hk (by cases digits <;> decide)
    · have ej : 2 * (l / 2) + 1 = l := by omega
      have hsub := subs_att hS hR hZ hG (g := l / 2) (by omega)
      rw [ej] at hsub
      have hk : (kindsBeforeBatching .attention (l == 0))[if digits then 6 else 1]? = some KindName.K3 := by
        unfold kindsBeforeBatching
        cases digits <;> rfl
      exact k3_alone O l .attention hsub _ hk (by cases digits <;> decide)

/-- **The same in one piece, from onlineDescription's value.** -/
theorem k3_alone_z {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (X : Verify.Public) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat)
        (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧ publicOf P.pol P.KL (some lay) = .ok X ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧ G₀.W = X ∧
      ProofFile.onlineSharedChain Z = some A ∧ ProofFile.onlineLastChain Z = some B ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ l < 25, ∀ digits : Bool, ∃ (Lk : Link S Cl) (b b' : Block S Cl),
        c.links[l]? = some Lk ∧ Lk.hear[k3Ix l digits]? = some b ∧
        k3At X Z (k3Place l digits) = some b' ∧
        LaidAlone ProofFile.sameReply b b' b.name (k3Place l digits) := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := seat_open hF
  exact ⟨Bs.G₀.W, Z, Bs.G₀, c, A, B, O.pub, O.public, O.blank, rfl, O.shared, O.second, O.desc,
    k3_of hS hR O⟩

/-- **The seated block's yes is the kind's own block's yes**, with no mark behind it and the reply as it was. -/
theorem k3_yes {b b' : Block S Cl} {name : String} {l : ℕ} {digits : Bool}
    (h : LaidAlone ProofFile.sameReply b b' name (k3Place l digits)) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) :
    b.decide s rs gs = .ok t ↔
      b'.decide s rs gs = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true :=
  yes_alone h (fun e => nomatch e) s t rs gs

end IM

#print axioms IM.theStated_place
#print axioms IM.k3Hear_mem
#print axioms IM.k3_alone
#print axioms IM.k3_of
#print axioms IM.k3_alone_z
#print axioms IM.k3_yes
