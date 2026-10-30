-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05AtMgRow.lean: kind K5: THE FIELD "behind" OF K5AtMg (Att/K05AtMgBehind.lean: k5AtMg_behind_door) WITH THE THREE PREMISES ON THE TABLE's ROW PAID BY THE TABLE's OWN TEXT: o1, o2 (the items formsT m 3 "own" and formsT m 2 "join" are among
what block number k opens) and hopen (pin m 0 is in its context): from Ix : K5Place links m pl pl' (the place is piece 3 of the attention segment m) and hk : pls[k]? = some pl. With them three letters for one number fall into one: m · x.link (hxm : x.link = m) ·
the pin's segment.
Also: K5Book (Att/K05T2.lean: the kind's sub-protocol tells no oracle message: the table's two numbers by place stay) from the test on the numbers bookFit (Johnson/Desc/First/BookFit.lean), and that the kind's block tells none.
Main names: k5_own_open · k5_join_open · k5AtMg_behind_row · k5Book_of_fit · k5AtN_tells_none.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05AtMgBehind
import Johnson.Desc.First.BookFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open VerifiableInference.Desc (Wit Place)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Item)
open VerifiableInference.Desc.K9 (Readers segAt? atMoment1)
open VerifiableInference.Desc.Sound (Alike SmpBySeat)
open VerifiableInference.Desc.Sound (Stated Mem msgsOf MsgT formsTQ seatTab Frame strsOf relAt meansQ outsQ
  second)
open VerifiableInference.Desc.First.Look (Sent JAtt attSg sigListCalls bornAt)
open K5Law (funsAt inAt_is firstAt_is secondAt_is readers_at runsN_is)
open VerifiableInference.Desc.K9 (Read lateOf ownRow readerOf RunOf runOfForms)

open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound (Sending pinJT)

open VerifiableInference.Desc.First (Pub)
open VerifiableInference.Desc.First.Look (enMask)
open VerifiableInference.Desc.First (rowOf segRow bookFit bookFit_at told_succ_nil)
open VerifiableInference.Desc.Sound (rowQ)

/-- formsT m 3 "own" is among what the kind's row opens: by the table's text. -/
theorem k5_own_open {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl pl' : Place} (Ix : K5Place links m pl pl')
    (hk : ps[k]? = some pl) : outsQ links ps k (.formsT m 3 "own") := by
  unfold outsQ rowQ
  rw [hk]
  show Item.formsT m 3 "own" ∈ (rowOf links pl).outs ++ (rowOf links pl).ctx ++ [.unmarked]
  rw [k5_row Ix, k5_outs]
  simp

/-- formsT m 2 "join" likewise. -/
theorem k5_join_open {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl pl' : Place} (Ix : K5Place links m pl pl')
    (hk : ps[k]? = some pl) : outsQ links ps k (.formsT m 2 "join") := by
  unfold outsQ rowQ
  rw [hk]
  show Item.formsT m 2 "join" ∈ (rowOf links pl).outs ++ (rowOf links pl).ctx ++ [.unmarked]
  rw [k5_row Ix, k5_outs]
  simp

/-- **The field "behind", the row's three premises paid.** -/
theorem k5AtMg_behind_row {Cells Tok Cl Pp Xi : Type} {Fr : Frame} (base : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (m : ℕ)
    (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ)
    (x0 : Pp → First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → First.S × Fr.E.Str → Forest.Heard) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl) (N : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (links : List ModelPart) (pl : Place) (O : List Item) (Q : List Pub)
    (leftIs : ∀ π : Pp, ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork
        (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
        (fun F => Room F ns x.F.next
          (Forest.elems x.fs + (slotsOf (script (parO Wv m a before).own) + 0))) ((x0 π) a') ((gOf π) a') a'.1)
    (hfs : x.fs = a.fs) (hleftQ : Pub.left m ∈ Q) {pl' : Place} (Ix : K5Place links m pl pl') (hxm : x.link = m)
    (Gd : FileDescription Xi) (Rds : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String))
    (uL uH : ℕ → VerifiableInference.Desc.Sound.UFn)
    (pls : List Place) (k : ℕ)
    (arrN : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (hi : ℕ)
    (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((Johnson.Pack.sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (hlow : ∀ i, (seat i).1 < base)
    (hfT : ∀ (π : Pp) (j : ℕ) (name : String) (b : First.S × Fr.E.Str) (w : Wit Cells Tok MsgT),
      Mg.formsT x.link j name (π, b.1) (strsOf Fr b.2) w →
      ∀ p ∈ runs x.link j name, formsTQ (Rds x.link) (Stated.of (VerifiableInference.Desc.Sound.uBySort uL (uArm Wv) uH)) (N.sent x.link 0) p.1 p.2 b.1
        (seatTab D.codes arrN ms w))
    (hpub : TiePub D x a.seam.tl hi rad)
    (r1 : (2, "first") ∈ runs x.link 3 "own") (r2 : (2, "second") ∈ runs x.link 3 "own")
    (r3 : (2, "join") ∈ runs x.link 2 "join")
    {states : ℕ → List (VerifiableInference.Desc.K9.RunOf First.S)}
    (hRds : ∀ (name : String) (s : First.S) (R : VerifiableInference.Desc.K9.Read), (name == "K8.equations") = false →
      readerOf states 2 name s = some R → (Rds x.link).forms 2 name s = some R)
    (hst : states 2 = runsN a)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr a.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hA : Wv.A[x.link / 2]? = some a) (hP : K5Law.OfPlan a)
    (hdoor : ∀ (π : Pp) (a' : First.S × Fr.E.Str), onT N Mg links π Fr pl O Q a' →
      DoorYes Wv x D (VerifiableInference.Desc.First.Look.bornAt D x.link) (VerifiableInference.Desc.First.Look.keptAt D x.link).length
        (N.sent x.link 0)
        (psOf (sigListCalls D rad x.link) seat (readMsgs D x a.seam.tl))
        (qsOf (sigListCalls D rad x.link) (readMsgs D x a.seam.tl)) hi (gOf π a') a'.1)
    (smp : Pp × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((Johnson.Pack.sigOf D.codes s.l).om i).Smp)
    (hpin : Mg.pin = pinJT D.codes Gd arrN smp ms)
    (hsome : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls D rad x.link, seat⟩, i⟩ : Mem)) (hSB : SmpBySeat D.codes smp)
    (hsent : ∀ i, seat i ∈ N.sent m 0)
    (hsm : ∀ (π : Pp) (s : First.S) i, smpR (s.st.oracles, s.book) i = smp (π, s) ⟨sigListCalls D rad x.link, seat⟩ i)
    (hk : pls[k]? = some pl) :
    ∀ π : Pp, K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv m a before) ns base a.nW (plannedK a)
      (padOfO a.fs) [] (gOf π) (onT N Mg links π Fr pl O Q)
      (k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smpR arrN Fr base hlow)
      (relAt (meansQ (Fr := Fr) N Mg fun s => (π, s)) (outsQ links pls k)) :=
  k5AtMg_behind_door base claim Wv m before a x D rad Ex Wp α ns x0 gOf plJ N Mg links pl O Q leftIs hfs hleftQ Gd Rds runs uL uH
    pls k arrN seat ms hi smpR hlow hfT (hxm ▸ k5_own_open Ix hk) (hxm ▸ k5_join_open Ix hk) hpub r1 r2 r3 hRds hst hm hA hP hdoor m smp hpin
    (H2K5.Door.k5_pin_open Ix hk) hsome hSB hsent hsm

/-- **K5Book, from the test on the table's numbers.** told: what each block of the chain tells. -/
theorem k5Book_of_fit (N : Numbers) (ps : List Place) (told : List (List Oracle)) (hf : bookFit N ps told = true) {k : ℕ}
    (hk : k < ps.length) (hn : told[k]? = some []) {pl pl' : Place} (h0 : ps[k]? = some pl) (h1 : ps[k + 1]? = some pl') :
    K5Book N pl pl' := by
  have a := bookFit_at N ps told hf k (Nat.le_of_lt hk)
  have b := bookFit_at N ps told hf (k + 1) hk
  have c := told_succ_nil told k hn
  rw [h0] at a
  rw [h1] at b
  exact ⟨by rw [b.1, a.1, c.1], by rw [b.2, a.2, c.2]⟩

/-- The kind's block tells no oracle message, at any of its rounds. -/
theorem k5AtN_tells_none {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)}
    {b' : VerifiableInference.Desc.Block First.S VerifiableInference.Desc.Claim} (hb : k5AtN W l g before = some b') :
    ∀ o ∈ b'.oracles, o = [] := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  intro o ho
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 ho
  rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5AtMg_behind_row
#print axioms VerifiableInference.Desc.First.Att.P.k5Book_of_fit
#print axioms VerifiableInference.Desc.First.Att.P.k5AtN_tells_none
