-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K6Seat.lean.
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K6's block (the output head's own
rounds) at its place in onlineDescription's first chain.
OBJECT. THE SEATED CONSTANT: VerifiableInference.Desc.Kinds.Head.seatedClaims X 24 ms (Johnson/Stored/HeadAddsAtS.lean), at ms given by
P4.headBefore Z G₀ (Johnson/Desc/ProofFile/Lot/K6K7.lean), as it stands at F.first.links[24].hear[3] for F := ProofFile.onlineDescription's value.
USER. K06's law «at the seated block» and its rows at the place; the planes' row.
LETTERS. P · pp · F: the goals' public files, what readFiles makes of them, onlineDescription's value · lay: ANY BYTES (the theorem never reads P.lay; the goals' caller lays lay := P.lay, which InScope pins).
HANDED OUT, EACH BY AN EQUATION THAT MAKES IT:
  Z: ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = ok Z · X: publicOf P.pol P.KL (some lay) = ok X · G₀: ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀, with G₀.W = X ·
  A | B: ProofFile.onlineSharedChain Z = some A | ProofFile.onlineLastChain Z = some B · c: F = fileDescBy … c · Lk | b: c.links[24]? = some Lk | Lk.hear[3]? = some b ·
  ms: P4.headBefore Z G₀ = some ms · b': seatedClaims X 24 ms = some b'. NO WITNESS STANDS UNDER A BARE «there is». IN THE ONE-PIECE FORM c IS PINNED THROUGH THE DEPENDENT RECORD ALONE (F.first is c by rfl
  only behind «subst F»): A CALLER DOES BEST TO OPEN ONCE (Johnson/IMR/SeatOpen.lean: seat_open) AND
    CALL k6_of: there c is pinned by chainBy's own equation (Open.unique).


THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): what needs no scope stands at every o; what stands on a law of the library over «publicOf … = .ok X» stands at OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut).

  k6_of             THE SAME AS k6_alone_z, AT THE LETTERS OF AN OPENING (Johnson/IMR/SeatOpen.lean:
                    Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B; X := Bs.G₀.W, G₀ :=
                    Bs.G₀): for a caller who
                    wants several seats about ONE chain c: open once (seat_open), then call ‹kind›_of at the same letters.
  k6_alone_z        WHERE onlineDescription RETURNS F, in the goals' scope: link 24's fourth block in front of the batching IS
                    seatedAs ProofFile.sameReply b' b.name ⟨1, some 24, 4, K6⟩ (SeatForm.lean: LaidAlone): the seated block b', marked by ProofFile.guardMark, at the driver's
                    address, behind the driver's guard on the reply: NOTHING IS JOINED BEHIND IT. UNDER b's OWN NAME: b.name stands on both sides: WHICH STRING IT IS, IS NOT SAID (a name is
                    read for a refusal's words and the table of places alone); the other eight fields are pinned. G₀.built.size = 25 is handed out beside (the lot writes «G.built.size - 1»). AND THE POLICY AND THE NORM's NUMBERS THAT
                    Means READS AT THE HEAD ARE THAT SHAPE's: pp.pol = Hd.polOf X.hS · pp.nf =
                      Hd.npOf X.hS (readings_agree, Johnson/Goal/Meaning/Ties.lean).
  k6_yes            SO (yes_alone at K6's address): b.decide s rs gs = ok t ↔ b'.decide s rs gs = ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true.
  k6_step           the like at Block.step (step_alone): b.step ft s rs cols = ok (t, k) ↔ b'.step ft s rs cols = ok (t, k) ∧ t.failed = none ∧ sameReply s t = true; sameReply_eq makes the last an equation
                    s.out.reply = t.out.reply. For «F.first.blocksInOrder = pre ++ b :: post»: hear_split
                      (Johnson/IMR/PureChain.lean) at c.links[24]? | Lk.hear[3]?. For «W is free of
                      the request»: Open.W: Bs.G₀.W = Z.p.X.
  k6_run            a run of claims that is looked up by name in b is the guard around the run of that name looked up in b' (claim_yes at K6's address). NO «no mark» HERE: guardMark wraps the
                    decision alone: a run that marks S.failed and goes on passes at the place. «The reply as it was» is the Bool ProofFile.sameReply … = true (== on the reply's seat).
  The fields: alone_planOk | _rounds | _oracles | _before | _place (Johnson/IMR/SeatForm.lean).

WHERE THE PREMISES COME FROM. InScope · readFiles: the goals' own, in these very terms. onlineDescription secondHashFunction … = ok F: in a proof about a verifier that lays onlineDescription: by a case split on onlineDescription secondHashFunction P.pol P.lay P.KL (the error's arm
is that verifier's refusal): none in this file; `P5J.LaidAt`'s field value is that return (Johnson/P5J/LaidOpens.lean). Whether the three hold together (onlineDescription secondHashFunction returns in scope) is no theorem over the scope: it is proved at VerifierAndGoals.storedPublicFiles and
VerifierAndGoals.zGap alone (a member of the head: AtFullSide/Top/). A run's print tests for emptiness and pays hF to no Lean term.
What is not claimed. Nothing on what seatedClaims' block decides or states (K6's laws). Nothing on K7's place, on the lookup's block at hear[2]. NOTHING ON Lk.order | each | batch | tests | number: so k6_run has an
object only where somebody shows that the frame looks up (3, «norm» | «join» | «policy» | «logits») in this Lk. A law that CONCLUDES a yes of b' passes to b only with «no mark» and «the reply as it was». No soundness.
-/
import Johnson.IMR.LaidFirst
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs
import Johnson.Goal.Meaning.ScopeCore
import Johnson.Goal.Meaning.Ties

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open Inst.Model
open OnBytes OnBytes.Road OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)
open ProofFile (Cl)

/-- K6's address. -/
abbrev k6Place : Place := { chain := 1, link := some 24, piece := 4, kind := .K6 }

/-- **K6 AT THE HEAD's LINK: THE LOT's SEATED BLOCK, ALONE: AT AN OPENING's OWN LETTERS.** -/
theorem k6_of {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b b' : Block S Cl) (ms : List (ℕ × ℕ)),
      c.links[24]? = some Lk ∧ Lk.hear[3]? = some b ∧ P4.headBefore Z Bs.G₀ = some ms ∧
      VerifiableInference.Desc.Kinds.Head.seatedClaims Bs.G₀.W 24 ms = some b' ∧
      LaidAlone ProofFile.sameReply b b' b.name k6Place ∧ Bs.G₀.built.size = 25 ∧
      pp.pol = Hd.polOf Bs.G₀.W.hS ∧ pp.nf = Hd.npOf Bs.G₀.W.hS := by
  have hZ := O.pub
  have hG := O.blank
  have hX := O.public
  obtain ⟨sz, -⟩ := ground_gets hS hR hZ hG
  have hk : (kindsBeforeBatching .head (24 == 0))[3]? = some KindName.K6 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    chain_hear_alone O.made O.places O.chain 24 .head (subs_head hS hR hZ hG) 3 .K6 hk (by decide)
      (by decide) (by decide)
  obtain rfl : L = P4.k6Lot Z := lot_of_kind hL hb' (by rw [ep]; rfl)
  have hb'' : b' ∈ ((P4.headBefore Z Bs.G₀).bind fun ms =>
      VerifiableInference.Desc.Kinds.Head.seatedClaims Bs.G₀.W (Bs.G₀.built.size - 1) ms).toList := by
    rcases blocks_mem hb' with ⟨x, hx, -⟩ | h
    · exact nomatch hx
    · exact h
  rw [Option.mem_toList, sz] at hb''
  obtain ⟨ms, hms, hsc⟩ := Option.bind_eq_some_iff.1 hb''
  have Acore := Hd.core_of_scope hS hR hX
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree P pp (some lay) Bs.G₀.W hR hX
  have tS := tS (Acore.num 2)
  have en : pp.nf = (scalesAt Bs.G₀.W).nf := congrArg Cm.Scales.nf tS
  have hla' : LaidAlone ProofFile.sameReply b b' b.name k6Place := by
    rw [alone_name hla]
    exact hla
  exact ⟨Lk, b, b', ms, e1, e2, hms, hsc, hla', sz, tP, en⟩

/-- **The same in one piece, from onlineDescription's value.** -/
theorem k6_alone_z {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (X : Verify.Public) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat)
        (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧ publicOf P.pol P.KL (some lay) = .ok X ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧ G₀.W = X ∧
      ProofFile.onlineSharedChain Z = some A ∧ ProofFile.onlineLastChain Z = some B ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∃ (Lk : Link S Cl) (b b' : Block S Cl) (ms : List (ℕ × ℕ)),
        c.links[24]? = some Lk ∧ Lk.hear[3]? = some b ∧ P4.headBefore Z G₀ = some ms ∧
        VerifiableInference.Desc.Kinds.Head.seatedClaims X 24 ms = some b' ∧
        LaidAlone ProofFile.sameReply b b' b.name k6Place ∧ G₀.built.size = 25 ∧
        pp.pol = Hd.polOf X.hS ∧ pp.nf = Hd.npOf X.hS := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := seat_open hF
  exact ⟨Bs.G₀.W, Z, Bs.G₀, c, A, B, O.pub, O.public, O.blank, rfl, O.shared, O.second, O.desc,
    k6_of hS hR O⟩

/-- **The seated block's yes is the lot's block's yes**, with no mark behind it and the reply as it was. -/
theorem k6_yes {b b' : Block S Cl} {name : String} (h : LaidAlone ProofFile.sameReply b b' name k6Place)
    (s t : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    b.decide s rs gs = .ok t ↔
      b'.decide s rs gs = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true :=
  yes_alone h (by decide) s t rs gs

/-- **THE GUARDS OFF, AT THE STEP**: the seated block's step goes on just where the lot's block's does, with no mark behind it and the reply unturned. -/
theorem k6_step {b b' : Block S Cl} {name : String} (h : LaidAlone ProofFile.sameReply b b' name k6Place)
    (ft : ℕ) (s t : S) (k : ℕ) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) :
    b.step ft s rs cols = .ok (t, k) ↔
      b'.step ft s rs cols = .ok (t, k) ∧ t.failed = none ∧ ProofFile.sameReply s t = true :=
  step_alone h (by decide) ft s t k rs cols

/-- **A run of claims looked up in the seated block is the guard around the lot's block's run of that name.** -/
theorem k6_run {b b' : Block S Cl} {name : String} (h : LaidAlone ProofFile.sameReply b b' name k6Place)
    {n : String} {r : ℕ → S → Except String (List Cl × S)} (hr : b.claims.lookup n = some r) :
    ∃ r', b'.claims.lookup n = some r' ∧ r = guardRun ProofFile.sameReply r' ∧
      ∀ k t y, r k t = .ok y ↔ r' k t = .ok y ∧ ProofFile.sameReply t y.2 = true :=
  claim_yes h hr

end IM

#print axioms IM.k6_of
#print axioms IM.k6_alone_z
#print axioms IM.k6_yes
#print axioms IM.k6_step
#print axioms IM.k6_run
