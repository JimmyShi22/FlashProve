-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TieRoad.lean: the road from "a sampled message has no candidate" to "few draws
at which the batched claim has a witness", at any word that holds the message's sent word at a seat.
Statements and proofs.

No second group is needed, and there is no new mathematics.
Why: Johnson/Desc/K12/Law/NoneNearCand.lean spoke of the word of a group of its own make
(`gpOfList`: each member's format from its own shape), the law of the proximity test of the word of
another (`gpG`: the stage's two codes, the tree's depth). An equation of the two groups' words wants
the members' sent words in two types that part (`Mb.cd.Word` reads M.C.a and M.a). It is not needed:
the library's lemma "a share of a jointly close word is close" (`Site.share`,
OnBytes/Slice/KeyGroup.lean) asks of the word on the stage's tables one thing, `Site.Tie`: that it
holds the sent word at the seat's rows. So every statement here takes any y : s.cIn.Word with
`Site.Tie`, for one message.
Main names:
  `noneNear_of_noCand1`: from one sampled message (shape sh, radius e0), a seat σs : Site s
    (mbOfShape cs sh e0), its word as sent f, y with σs.Tie (upW f) y, e fitting e0 in leaves, hS
    for near witnesses (`answers_of_says_g`, Johnson/Desc/K12/Law/FormTake.lean, pays it at the row
    that the record holds) and no candidate: `NoneNear s e S' L rows y`.
  `few_draws_of_noCand1`: with `batCatches_joh`: cnt (BadDraws …) ≤ s.lstJ e · (rows.size − 1).
  `codeIs_eq`, `siteOf`, `siteOf_pM`, `siteOf_pZ`: the seat exists where `siteL` says yes
    (Johnson/Desc/K12/Law/SiteOk.lean): its five clauses on the fields of `Site` give a seat by
    numbers (the library's `Site.byNo`) at `sgOf a`; the premises hpM and hpZ of `words_share` hold
    of it by rfl.
  `ok_tagM`, `siteL_of_ok`: the test's yes reaches each member: siteOk p t = true, at the plain data
    (a, D) that `plainAt` makes, gives ok (siteL D.st.codes a m) at every m ∈ D.mems, which is the
    premise of `siteOf`. So `siteOk` is no transcription: its yes inhabits the type at every member.
  `tie_of_gp`: the bridge at the level of the word: the word of any group G holds at a seat σ' of
    another format the word y', if row by row σ' sits where G's member i sits and y' reads what that
    member's sent word reads: values in the field alone.
At the law's group `gpG`: the numbers of rows of `mbOf` and `mbOfShape` are one by definition
(sh.mainRows, sh.maskRows), and both seats are by numbers from the same first rows: so in hM and hZ
r := r' and the seats' equation is rfl. What is left is the two equations of values: that upW f
reads, at the position x cast (main) or x modulo 2 ^ aOf (mask), what the law's written oracle reads
at x cast or x modulo 2 ^ (the tree's depth). Under the clause "depth" the two moduli are one
number. That assembly wants Johnson/Desc/K12/Law/FirstOkLaw.lean beneath and is not typed here (it
is `tie_gpG`, Johnson/Desc/K12/Law/TieYOf.lean); and which f is "the word as sent" is the tie at the
first stage.
Limits: the seed of hS (that the record's sample row is { Send.form … with target := the answer } at
some seed: Johnson/Desc/K12/Law/SampleOk.lean tests it at a record); `Site.Tie` at the law's word:
the two equations of values; members without a sample: nothing; it is a count of θ, with no game;
cs, sh, e0, f, smp and r are free letters; as in the files on the batching's converse under
Johnson/Desc/Means, which lie beneath: nothing on who draws the batching's element, or when, or on
how its readings are spread over the field. No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `Site.share`, `Gp.tie_word`
(OnBytes/Slice/KeyGroup.lean), `sig_inList_iff` (Cb/Ld/LdSigProofs.lean); `batCatches_joh`
(Johnson/Desc/K12/Law/NoneNearCand.lean).
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.ShareWords
import Johnson.Desc.K12.Law.SiteOk

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open H2K.First (Seat1)

/-- A sampled message without a candidate refutes the relation in front, at any word that holds
its sent word at a seat. One message: its shape sh and radius e0; σs: a seat in the stage s at the
format that the shape gives; f: its word as sent; y: any word on the stage's tables that holds f at
the seat's rows (the library's Site.Tie). No group stands in the statement. -/
theorem noneNear_of_noCand1 (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e0 : ℕ) {s : Sg}
    (σs : Site s (mbOfShape cs sh e0)) (f : (portOmZ cs sh e0).Str) (smp : (portOmZ cs sh e0).Smp)
    (e : ℕ) (hfit : e < (e0 + 1) * 2 ^ (s.C.a - aOf cs sh)) (y : s.cIn.Word)
    (hT : σs.Tie ((portOmZ cs sh e0).upW f) y) (S' : Statement) (L : GroupLayout) (rows : Array Row)
    (r : Row) (hr : r ∈ rows.toList)
    (hS : ∀ w : s.cIn.N.Wit, offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e →
      Says rdE S' r (H2K.ClaimSays.wordsOf S' L (tabOf s w.1)) →
      (portOmZ cs sh e0).Z.val smp.1 (fun j => w.1 (σs.atJ j)) = smp.2)
    (hno : ∀ m, ¬ (portOmZ cs sh e0).Cand f smp m) : NoneNear s e S' L rows y := by
  intro w hn hall
  obtain ⟨r', hr'⟩ := σs.share hT hfit w hn
  exact hno _ ⟨(sig_inList_iff GE (portOmZ cs sh e0) f _).1 ⟨(_, r'), hr', rfl⟩, hS w hn (hall r
      hr)⟩

/-- With the batching's converse at the Johnson bound's list. -/
theorem few_draws_of_noCand1 (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e0 : ℕ) {s : Sg}
    (σs : Site s (mbOfShape cs sh e0)) (f : (portOmZ cs sh e0).Str) (smp : (portOmZ cs sh e0).Smp)
    (e : ℕ) (hJ : s.StageJ e) (hfit : e < (e0 + 1) * 2 ^ (s.C.a - aOf cs sh)) (y : s.cIn.Word)
    (hT : σs.Tie ((portOmZ cs sh e0).upW f) y) (S' : Statement) (g : Nat) (L : GroupLayout)
    (rows : Array Row) (ht : combineAt S' g ⟨L, rows⟩ = true) (hk : L.k = s.h + s.g) (hh : L.h =
        s.h)
    (hl : 2 ^ L.logEll = s.C.l) (hz : 2 ^ L.logEllZk = s.Z.l) (r : Row) (hr : r ∈ rows.toList)
    (hS : ∀ w : s.cIn.N.Wit, offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e →
      Says rdE S' r (H2K.ClaimSays.wordsOf S' L (tabOf s w.1)) →
      (portOmZ cs sh e0).Z.val smp.1 (fun j => w.1 (σs.atJ j)) = smp.2)
    (hno : ∀ m, ¬ (portOmZ cs sh e0).Cand f smp m) :
    cnt (BadDraws s e S' g L rows y) ≤ s.lstJ e * (rows.size - 1) :=
  batCatches_joh s e hJ S' g L rows y ht hk hh hl hz
    (noneNear_of_noCand1 cs sh e0 σs f smp e hfit y hT S' L rows r hr hS hno)

theorem codeIs_eq {c : OnBytes.Code} {x : Fmt.M1.Code} (h : codeIs c x = true) : codeOf c = x := by
  have h' : c = ⟨x.a, x.l, x.r⟩ := of_decide_eq_true h
  rw [h']
  rfl

/-- The seat exists where siteL says yes: the five clauses on Site's fields
(Johnson/Desc/K12/Law/SiteOk.lean) give a seat by numbers of the member's own format in the place's
first stage. oM, oZ: the rows at which its blocks begin. -/
def siteOf (K : OnBytes.Codes) (a : Fmt.M1.Stage) (m : Seat1) (e0 oM oZ : ℕ)
    (h : ok (siteL K a m) = true) : Site (H2K.Pub.sgOf a) (mbOfShape K m.sh e0) :=
  have h' : (aOfB K m.sh ≤ a.C.a) ∧ ((m.sh.mainRows == 0) = true ∨ codeIs (mainB K m.sh) a.C =
      true) ∧
      ((m.sh.mainRows == 0) = true ∨ aOfB K m.sh = a.C.a) ∧
      ((m.sh.maskRows == 0) = true ∨ codeIs (maskB K m.sh) a.Z = true) ∧
      ((m.sh.maskRows == 0) = true ∨ (maskB K m.sh).logN ≤ aOfB K m.sh) := by
    simp only [siteL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  Site.byNo (H2K.Pub.sgOf a) (mbOfShape K m.sh e0) oM oZ h'.1
    (fun h0 => ⟨codeIs_eq (h'.2.1.resolve_left fun q => by
        have : m.sh.mainRows = 0 := by simpa using q
        exact absurd h0 (by show ¬ 0 < m.sh.mainRows; omega)),
      h'.2.2.1.resolve_left fun q => by
        have : m.sh.mainRows = 0 := by simpa using q
        exact absurd h0 (by show ¬ 0 < m.sh.mainRows; omega)⟩)
    (fun h0 => ⟨codeIs_eq (h'.2.2.2.1.resolve_left fun q => by
        have : m.sh.maskRows = 0 := by simpa using q
        exact absurd h0 (by show ¬ 0 < m.sh.maskRows; omega)),
      h'.2.2.2.2.resolve_left fun q => by
        have : m.sh.maskRows = 0 := by simpa using q
        exact absurd h0 (by show ¬ 0 < m.sh.maskRows; omega)⟩)

theorem siteOf_pM (K : OnBytes.Codes) (a : Fmt.M1.Stage) (m : Seat1) (e0 oM oZ : ℕ)
    (h : ok (siteL K a m) = true) (r) : (siteOf K a m e0 oM oZ h).pM r = vtx _ (oM + r.val) := rfl

theorem siteOf_pZ (K : OnBytes.Codes) (a : Fmt.M1.Stage) (m : Seat1) (e0 oM oZ : ℕ)
    (h : ok (siteL K a m) = true) (r) : (siteOf K a m e0 oM oZ h).pZ r = vtx _ (oZ + r.val) := rfl

/-- The bridge, at the level of the word: the word of any group G of the library holds, at a
seat σ' of another format M', the word y', if row by row σ' sits where G's member i sits and y'
reads what that member's sent word reads. No equation of groups, of formats or of types is asked:
only values in the field. -/
theorem tie_of_gp {s : Sg} (G : Gp s) (hA : G.Apart) (yw : G.Words) (i : G.ι) {M' : Mb}
    (σ' : Site s M') (y' : M'.cd.Word)
    (hM : ∀ (x : Fin (2 ^ s.C.a)) (r' : Fin M'.nM), ∃ r : Fin (G.mb i).nM,
      (G.seat i).pM r = σ'.pM r' ∧
      yw i (.inl (Fin.cast (congrArg (fun C : Fmt.M1.Code => 2 ^ C.a) ((G.seat i).hC r).symm) x))
          (r, ()) =
        y' (.inl (Fin.cast (congrArg (fun C : Fmt.M1.Code => 2 ^ C.a) (σ'.hC r').symm) x)) (r', ()))
    (hZ : ∀ (x : Fin (2 ^ s.C.a)) (r' : Fin M'.nZ), ∃ r : Fin (G.mb i).nZ,
      (G.seat i).pZ r = σ'.pZ r' ∧
      yw i (.inr (Site.red (G.mb i) x)) (r, ()) = y' (.inr (Site.red M' x)) (r', ())) :
    σ'.Tie y' (G.word yw) where
  main := fun x r' => by
    obtain ⟨r, h1, h2⟩ := hM x r'
    rw [← h1, ((G.tie_word hA yw).mem i).main x r, h2]
  mask := fun x r' => by
    obtain ⟨r, h1, h2⟩ := hZ x r'
    rw [← h1, ((G.tie_word hA yw).mem i).mask x r, h2]

theorem ok_tagM (j : ℕ) (l : Clauses) : ok (tagM j l) = ok l := by
  unfold ok tagM
  rw [List.all_map]
  rfl

/-- The test's yes reaches each member: siteOk p t = true, at the plain data that the place
and the record behind the batching make, gives the six clauses' yes at every member: so siteOf's
premise. -/
theorem siteL_of_ok (p : VerifiableInference.Desc.K12.P12) (t : VerifiableInference.Desc.K12.T12)
    (a : Fmt.M1.Stage) (D : H2K.First.Plain) (hp : plainAt p t = some (a, D))
    (h : siteOk p t = true) (m : Seat1) (hm : m ∈ D.mems) : ok (siteL D.st.codes a m) = true := by
  unfold siteOk siteAll at h
  rw [hp] at h
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
  have hz : (m, i) ∈ D.mems.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    rw [List.getElem?_eq_getElem hi, e]
  have h2 : ∀ c ∈ tagM i (siteL D.st.codes a m), c.2 = true := fun c hc =>
    (List.all_eq_true.1 h) c (List.mem_flatMap.2 ⟨(m, i), hz, hc⟩)
  rw [← ok_tagM i]
  exact List.all_eq_true.2 h2

end H2K.Pin

#print axioms H2K.Pin.siteL_of_ok
#print axioms H2K.Pin.few_draws_of_noCand1
#print axioms H2K.Pin.siteOf
#print axioms H2K.Pin.tie_of_gp
