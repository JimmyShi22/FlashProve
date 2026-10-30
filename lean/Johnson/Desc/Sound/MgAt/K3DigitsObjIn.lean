-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsObjIn.lean: the lookup on the digits of a segment's approximate
range proof: THE ONE PUBLIC TEST OF THE COMPOSED MEANING THAT IS NEW BEHIND THE DIGITS' SUB-PROTOCOL
AND NONE OF THE KIND's OWN: formsIn l (7 + shift sub) "objects" (its runs: "objects" and "guests" at
the digits' own piece), AT THE STATE BEHIND AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL. After the
like at the calls (MgAt/K3CallsObjIn.lean). At the sub-protocol's own decide, whatever the rounds'
words. Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  digits_behind_named: behind the whole seated accept: a ledger with its sizes, what was heard at
    the digits' seat, and every heard row names filled slots of that ledger alone (decide_named,
    Johnson/Top/H/Keep/K3Named.lean; the step without a round: quietAt_pass, quietAt_tlFuns).
  formsIn_make_mgAll: KIND-FREE: where each run that the table's name stands for is none of the
    approximate range proof's own and its test formsIn holds at s, the composed test at formsIn l k
    r holds at s.
  objIn_dig: THE END: by objects_formsIn, guests_formsIn (Johnson/Top/H/Keep/FormsInObjects.lean).
WHAT IT STILL CARRIES, BOOKED.
  AT THE STATE BEHIND, WITH A FACT ALONG THE FOLD: hmask (the mask row's message is sent and the
    book seats it among the segment's own) · hmerge (no heard row names the slot of the merge's end
    value).
  TERMS OF Dm: hlinks · hRd · he · hA · pass with hpass, hsame · hfO, hfG.
  ON THE STATE IN FRONT: hF, hS (the ledger with its sizes).
OBJECT. The composed public test at formsIn; Desc.K3.theStated's value at the digits' address.
Used by K3DigitsObjInFits.lean (Johnson/Desc/Sound/MgAt/).
LETTERS. Those of MgAt/K3DigitsFormsOurs.lean; pass.


Compiled with the whole library.


Limits. At Cl := Desc.Claim.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsInObjects
import Johnson.Top.H.Keep.K3Named
import Johnson.Desc.Sound.MgAt.K3CallsObjIn
import Johnson.Desc.Sound.MgAt.K3DigitsFormsSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning runsOf pubAll_formsIn)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles formsIn maskSeat
  mergeOf)

/-- **Behind the whole seated accept.** -/
theorem digits_behind_named {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) :
    ∃ (G : Fork) (g : Forest.Heard), s₂.fork? = some G ∧
      (Desc.K3.seatDigits claim).heard s₂ = some g ∧ _root_.Fo.Tp.NamedAll G g.rows ∧
      OnBytes.PscRun.Sized G := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  obtain ⟨F1, y, hF1, hn1, e1, hN⟩ :=
    decide_named (Desc.K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((Desc.K3.seatDigits claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : (Desc.K3.seatDigits claim).heard s' = some y.1 := by
    rw [e1]
    exact Desc.K3.seatDigits_reads claim _ _ _ hsome hn1
  have hF1' : s'.fork? = some y.2 := by
    rw [e1]
    exact seatDigits_keeps claim _ _ _ hsome hn1
  obtain ⟨G0, Q0⟩ := k3_digits_pass claim a.piece laid sent P' [] s s' _ gs' hyes hF hS
  have eG0 : G0 = y.2 := Option.some.inj (Q0.behind.symm.trans hF1')
  have hSz : OnBytes.PscRun.Sized y.2 := eG0 ▸ Q0.sizedG
  have hNm : _root_.Fo.Tp.NamedAll y.2 y.1.rows := (hN hS).rows
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact ⟨y.2, y.1, hF1', hg1, hNm, hSz⟩
  · obtain ⟨G₂, Q₂⟩ := quietAt_pass X i f hf s' s₂ hfs hF1' hSz
    obtain ⟨et, -⟩ := quietAt_tlFuns X i f hf s' s₂ hfs
    have hg2 : (Desc.K3.seatDigits claim).heard s₂ = some y.1 := by
      show s₂.tl?.bind (·.heard) = some y.1
      rw [et]
      exact hg1
    refine ⟨G₂, y.1, Q₂.behind, hg2, hNm.later ?_, Q₂.sizedG⟩
    first
      | exact Q₂.later
      | exact ⟨Q₂.later.next, Q₂.later.ns, fun _ => Q₂.sizedG, Q₂.later.keep⟩

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **THE COMPOSED TEST AT formsIn HOLDS WHERE ITS RUNS' TESTS HOLD.** -/
theorem formsIn_make_mgAll (hlinks : Dm.links = linksFull) {l : ℕ} {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) {k : ℕ} {r : String} (z : P) (s : Desc.First.S)
    (hp : ∀ p ∈ runsOf sub k r, (p.2 == "K8.equations") = false ∧
      formsIn (Dm.Rd l) (Dm.N.group l) p.1 p.2 s = true) :
    (mgAll Dm Mg).pub (.formsIn l k r) (z, s) = true := by
  rw [mgAll_pub, pubAll_formsIn]
  have e : Dm.pubD.runs l k r = runsOf sub k r := by
    show runsAt Dm.links l k r = runsOf sub k r
    rw [hlinks]
    exact runsAt_of linksFull l sub hsub k r
  rw [e, List.all_eq_true]
  intro p hpm
  obtain ⟨ha, hq⟩ := hp p hpm
  have ea : Dm.pubD.ah p.1 p.2 = false := ha
  rw [ea]
  simp only [Bool.false_eq_true, if_false]
  exact hq

/-- **THE NEW ITEM.** -/
theorem objIn_dig (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
    (claim : Aff → Desc.Claim)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hlinks : Dm.links = linksFull) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    (hRd : Dm.Rd l = readersOfLink H lk) (hA : AtS2 (Desc.K3.seatDigits claim))
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) {k B₀ : ℕ}
    (he : runsOf sub k "objects" = [(B₀, "objects"), (B₀, "guests")])
    (pass : Desc.First.S → Desc.First.S → Prop) (hpass : ∀ t G, pass t (t.putFork G))
    (hsame : ∀ t, pass t t)
    (hfO : ∃ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "objects") = some (n, r) ∧
      RunOver pass r (objectsRun (Desc.K3.seatDigits claim)))
    (hfG : ∃ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "guests") = some (n, r) ∧
      RunOver pass r (guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim))))
    (hmask : ∀ c, segAt? s₂ = some c → (maskSeat (Dm.N.group l) c).isSome = true)
    (hmerge : ∀ g, (Desc.K3.seatDigits claim).heard s₂ = some g → ∀ f ∈ g.rows.toList,
      ∀ y ∈ f.slots.toList, mergeOf s₂ ≠ some y.1) :
    (mgAll Dm Mg).pub (.formsIn l k "objects") (z, s₂) = true := by
  obtain ⟨G, g, hG, hg, hNm, hSz⟩ :=
    digits_behind_named claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd hF hS
  obtain ⟨Lc, hLc⟩ := link_some_of_fork hG
  obtain ⟨c, hc, -, hcF, -, -⟩ := segAt_make hLc hG (tl_some_of_fork hG)
  refine formsIn_make_mgAll Dm Mg hlinks hsub z s₂ (fun p hpm => ?_)
  rw [he] at hpm
  rw [hRd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  rcases hpm with rfl | rfl
  · exact ⟨(by decide : ("objects" == "K8.equations") = false),
      objects_formsIn H lk B₀ (Dm.N.group l) (Desc.K3.seatDigits claim) hA pass hpass hfO hc hg
        (by rw [hcF]; exact hNm) (by rw [hcF]; exact hSz) (hmask c hc) (hmerge g hg)⟩
  · exact ⟨(by decide : ("guests" == "K8.equations") = false),
      guests_formsIn H lk B₀ (Dm.N.group l) pass hsame hfG hc⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digits_behind_named
#print axioms VerifiableInference.OnPublicFiles.formsIn_make_mgAll
#print axioms VerifiableInference.OnPublicFiles.objIn_dig
