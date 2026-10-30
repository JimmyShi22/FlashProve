-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K5Seat.lean. The seated block is k5Dress Z name b' := { b' with planOk := b'.planOk && (H2K5.k5Before? Z name).isSome }, b' given by k5AtN W l g ((H2K5.k5Before? Z name).getD []) = some b'.
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K5's block (an attention segment's own
rounds) at its place in
onlineDescription's first chain, seated at the public part's own attention plans.
OBJECT. THE SEATED CONSTANT: VerifiableInference.Desc.First.Att.P.k5AtN X (2 g + 1) g (H2K5.k5Before Z ("A" ++ toString g)) (Johnson/Desc/First/Att/SeatN.lean · Johnson/Desc/ProofFile/Lot/K5.lean: lotN),
as it stands at F.first.links[2 g + 1].hear[2], g < 12.
USER. K5's laws at the seated block; the attention rows (Means speaks at Hd.shapeA X g).
LETTERS. As in Johnson/IMR/K6Seat.lean; b': HANDED OUT BY k5AtN … = some b', every argument a term
of X, Z and g.


THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): what needs no scope stands at every o; what stands on a law of the library over «publicOf … = .ok X» stands at OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut).

  k5OwnN_mem        a block of K5's lot stems from a link Xl of kind 1 of the list, at its number l: k5AtN G.W l Xl.g (k5Before Z Xl.name) = some b.
  k5_of             at an opening's letters, in scope, for g < 12: link 2 g + 1's third block in front of the batching IS seatedAs sameReply b' b.name ⟨1, some (2 g + 1), 3, K5⟩: ALONE; X.A[g]? = some a ·
                    a.S = Hd.shapeA X g; AND a.own's twelve sizes are functions of the plan: OwnOfShape a and own_rows' equation (Johnson/Goal/Meaning/PlanOwn.lean, Johnson/Goal/Meaning/PlanOwnRow.lean). By k5AtN's text b' is
                    Att.P.attentionKind seatSO (runsN a) { link := 2 g + 1, piece := 3, work := …, own := a.own, before := … } with one more test on the plan (claimsOkAtO a).
  k5_alone_z        the same in one piece, from onlineDescription's value.
  k5_yes            yes_alone at K5's address.

WHO PAYS THE PREMISES: as in Johnson/IMR/K6Seat.lean: that onlineDescription returns in scope is a premise.
What is not claimed. Nothing on the seat seatSO, on the four runs' texts, on «before»'s numbers. No soundness.
-/
import Johnson.IMR.LaidFirst
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs
import Johnson.Goal.Meaning.PlanOwnRow

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open Inst.Model
open OnBytes OnBytes.Road OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

/-- K5's lot's dress: the block stands with «and "before" can be made» laid to its test on the plan. -/
abbrev k5Dress (Z : ProofFile.Pub) (name : String) (b : Block S Cl) : Block S Cl :=
  { b with planOk := b.planOk && (H2K5.k5Before? Z name).isSome }

/-- A block of K5's lot. -/
theorem k5OwnN_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} {b : Block S Cl} (h : b ∈ H2K5.k5OwnN Z G) :
    ∃ l Xl b₀, G.built[l]? = some Xl ∧ Xl.kind = 1 ∧
      VerifiableInference.Desc.First.Att.P.k5AtN G.W l Xl.g
        ((H2K5.k5Before? Z Xl.name).getD []) = some b₀ ∧ b = k5Dress Z Xl.name b₀ := by
  obtain ⟨x, hx, h1⟩ := List.mem_filterMap.1 h
  obtain ⟨b₀, h2, rfl⟩ := Option.map_eq_some_iff.1 h1
  unfold H2K5.k5Places at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
  obtain ⟨Xl, l⟩ := y
  refine ⟨l, Xl, b₀, ?_, by simpa using hy2, h2, rfl⟩
  rw [← Array.getElem?_toList]
  simpa using (List.mk_mem_zipIdx_iff_getElem?.1 hy1)

/-- K5's address at group g. -/
abbrev k5Place (g : ℕ) : Place := { chain := 1, link := some (2 * g + 1), piece := 3, kind := .K5 }

/-- **K5 AT THE ATTENTION LINKS: THE LOT's SEATED BLOCK, ALONE: AT AN OPENING's OWN LETTERS.** -/
theorem k5_of {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ g < 12, ∃ (Lk : Link S Cl) (b b' : Block S Cl) (a : Attention.Plan),
      c.links[2 * g + 1]? = some Lk ∧ Lk.hear[2]? = some b ∧
      VerifiableInference.Desc.First.Att.P.k5AtN Bs.G₀.W (2 * g + 1) g
        ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some b' ∧
      LaidAlone ProofFile.sameReply b (k5Dress Z ("A" ++ toString g) b') b.name (k5Place g) ∧
      Bs.G₀.W.A[g]? = some a ∧ a.S = Hd.shapeA Bs.G₀.W g ∧ Meaning.OwnOfShape a ∧
      a.own.rows = a.nLin +
        a.seam.tl.equationsF (Attention.tableReads a.S (Attention.Counts.of a.S)) := by
  intro g hg
  have hZ := O.pub
  have hG := O.blank
  have hX := O.public
  obtain ⟨nam, -⟩ := ground_named hS hR hZ hG
  obtain ⟨-, -, -, hA⟩ := Meaning.scope_plans hS hR hX
  obtain ⟨m, m', -, -, -, -, fm', km', gm', Nm'⟩ := nam g hg
  have hk : (kindsBeforeBatching .attention (2 * g + 1 == 0))[2]? = some KindName.K5 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    chain_hear_alone O.made O.places O.chain (2 * g + 1) .attention (subs_att hS hR hZ hG hg) 2 .K5
      hk (by decide) (by decide) (by decide)
  obtain rfl : L = H2K5.lotN Z := lot_of_kind hL hb' (by rw [ep]; rfl)
  have hb'' : b' ∈ H2K5.k5OwnN Z Bs.G₀ := by
    rcases blocks_mem hb' with ⟨y, hy, -⟩ | h
    · exact nomatch hy
    · exact h
  obtain ⟨l, Xl, b₀, eX, -, hat, rfl⟩ := k5OwnN_mem hb''
  have ep' : b₀.place = k5Place g := ep
  have el : l = 2 * g + 1 := by
    have e0 := (VerifiableInference.Desc.First.Att.P.k5AtN_states hat).2.2
    have e : (some l : Option ℕ) = some (2 * g + 1) := congrArg Place.link (e0.symm.trans ep')
    exact Option.some.inj e
  subst el
  obtain rfl : m' = Xl := Option.some.inj (fm'.symm.trans eX)
  rw [gm', Nm'.name] at hat
  rw [Nm'.name] at hla
  obtain ⟨a, ea, eS⟩ := hA g hg
  have hla' : LaidAlone ProofFile.sameReply b (k5Dress Z ("A" ++ toString g) b₀) b.name (k5Place g) := by
    rw [alone_name hla]
    exact hla
  exact ⟨Lk, b, b₀, a, e1, e2, hat, hla', ea, eS, Meaning.own_of_public hX ea,
    Meaning.own_rows hX ea⟩

/-- **The same in one piece, from onlineDescription's value.** -/
theorem k5_alone_z {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (X : Verify.Public) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat)
        (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧ publicOf P.pol P.KL (some lay) = .ok X ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧ G₀.W = X ∧
      ProofFile.onlineSharedChain Z = some A ∧ ProofFile.onlineLastChain Z = some B ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ g < 12, ∃ (Lk : Link S Cl) (b b' : Block S Cl) (a : Attention.Plan),
        c.links[2 * g + 1]? = some Lk ∧ Lk.hear[2]? = some b ∧
        VerifiableInference.Desc.First.Att.P.k5AtN X (2 * g + 1) g
          ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some b' ∧
        LaidAlone ProofFile.sameReply b (k5Dress Z ("A" ++ toString g) b') b.name (k5Place g) ∧
        X.A[g]? = some a ∧ a.S = Hd.shapeA X g ∧ Meaning.OwnOfShape a ∧
        a.own.rows = a.nLin +
          a.seam.tl.equationsF (Attention.tableReads a.S (Attention.Counts.of a.S)) := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := seat_open hF
  exact ⟨Bs.G₀.W, Z, Bs.G₀, c, A, B, O.pub, O.public, O.blank, rfl, O.shared, O.second, O.desc,
    k5_of hS hR O⟩

/-- **The seated block's yes is the lot's block's yes**, with no mark behind it and the reply as it was. -/
theorem k5_yes {b b' : Block S Cl} {name : String} {g : ℕ}
    (h : LaidAlone ProofFile.sameReply b b' name (k5Place g)) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) :
    b.decide s rs gs = .ok t ↔
      b'.decide s rs gs = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true :=
  yes_alone h (fun e => nomatch e) s t rs gs

end IM

#print axioms IM.k5OwnN_mem
#print axioms IM.k5_of
#print axioms IM.k5_alone_z
#print axioms IM.k5_yes
