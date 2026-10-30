-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallHead.lean: `Gathers` AND THE COUNT OF
Johnson/Desc/K8/Honest/FallCount.lean AT THE HEAD's SEGMENT's BATCHING. Statements and proofs. No
prover. Lemmas; none of the library's goals. NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR
HIDING.

By the general lemma `gathers_of_plain` (Johnson/Desc/K8/Honest/GathersPlain.lean): each run of
claims of the segment, but for "K8.equations", is free of the batching element; the two behind it
("logits", "the merge") also of the smallness test's data.
  `letters_re`, `letters_tl`, `planesAt_re`   all that the output head's own runs, its keys and its
      readers read of a state (Johnson/Desc/Kinds/HeadFrame.lean: lettersAt;
      Johnson/Stored/HeadSeatAt.lean: seatAt, planesAt) is the same where the batching element, or
      the smallness test's data, are replaced
  `lookup_map`, `plain_runsBy`, `plain_k6`   the output head's own runs ("norm", "policy",
      "logits"): they hand the state back
  `pscRow_ok`, `behind_merge`   the merge's run
  **`gathers_head`**   from the ties (`HeadTies`; the two at "objects"; tP: the run at (2, "planes")
      stands under the lookup's own at the head's readers, at some lm) and the order: at every state
      that holds data tl and a list of tables funs: `Gathers`, at SOME numbers and coefficients
  **`fall_few_head`**   so the count, in the form of `fall_few_layers`
Limits: the ties are premises. That a reached state's data pass `unitsLaid`, and the seat, are not
said here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallAtt
import Johnson.Desc.First.Link.Law.PayHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.K.Kc
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.Kinds.Head
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open OnBytes.Tie.Pv.Tail.Port (topOf)

/-! ## What the output head's runs read of a state -/

theorem letters_re (h : Model.Head.Shape) (iU3 : Nat) (p : Kinds.Head.Par) (θ : E) (s : S) :
    lettersAt p (seatAt h iU3) (reChi θ s) = lettersAt p (seatAt h iU3) s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    obtain ⟨fr, kept, ids, Lc, F, hx, ht, tl0, claim, wo, Fm, slot, opened, sq, lh⟩ := x
    cases opened <;> rfl
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem letters_tl (h : Model.Head.Shape) (iU3 : Nat) (p : Kinds.Head.Par) (tl : HTailF2) (s : S) :
    lettersAt p (seatAt h iU3) (s.putTl tl) = lettersAt p (seatAt h iU3) s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    obtain ⟨fr, kept, ids, Lc, F, hx, ht, tl0, claim, wo, Fm, slot, opened, sq, lh⟩ := x
    cases opened <;> rfl
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem planesAt_re (iU3 : Nat) (θ : E) (s : S) : planesAt iU3 (reChi θ s) = planesAt iU3 s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    obtain ⟨fr, kept, ids, Lc, F, hx, ht, tl0, claim, wo, Fm, slot, opened, sq, lh⟩ := x
    cases opened <;> rfl
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem callerKeys_re (h : Model.Head.Shape) (iU3 : Nat) (p : Kinds.Head.Par) (θ : E) (s : S) :
    callerKeys p (seatAt h iU3) (reChi θ s) = callerKeys p (seatAt h iU3) s := by
  unfold callerKeys
  rw [letters_re]

theorem callerReaders_re (iU3 : Nat) (θ : E) (s : S) :
    callerReaders (planesAt iU3) (reChi θ s) = callerReaders (planesAt iU3) s := by
  unfold callerReaders
  rw [planesAt_re]

/-! ## The output head's own runs -/

theorem lookup_map {α : Type} (F : String → α) : ∀ (names : List String) (name : String) (r : α),
    (names.map fun n => (n, F n)).lookup name = some r → r = F name
  | [], _, _, h => by cases h
  | n :: ns, name, r, h => by
    rw [List.map_cons, List.lookup_cons] at h
    cases hb : (name == n) with
    | true =>
      rw [hb] at h
      obtain rfl : name = n := by simpa using hb
      exact (Option.some.inj h).symm
    | false =>
      rw [hb] at h
      exact lookup_map F ns name r h

theorem plain_runsBy (names : List String)
    (runs : Given → Behind → Places → List (String × List Kinds.Form))
    (keys : Given → Behind → Places → List Kinds.Form) (p : Kinds.Head.Par)
    (h : Model.Head.Shape) (iU3 : Nat)
    (name : String) (r : Nat → S → Except String (List Claim × S))
    (hr : (runsBy names runs keys asClaim p (seatAt h iU3)).lookup name = some r) :
    PlainRun r ∧ PlainBehind r := by
  unfold runsBy at hr
  obtain rfl := lookup_map _ names name r hr
  have cut : ∀ (t : S) (y : List Claim × S),
      (do
        let (g, b, x) ← lettersAt p (seatAt h iU3) t
        let fs ← named "the run is there" ((runs g b x).lookup name)
        pure (fs.map asClaim,
          if names.head? == some name then (seatAt h iU3).setKeyForms t (keys g b x) else t) :
        Except String (List Claim × S)) = .ok y →
      ∃ z fs, lettersAt p (seatAt h iU3) t = .ok z ∧
        (runs z.1 z.2.1 z.2.2).lookup name = some fs ∧ y = (fs.map asClaim, t) := by
    intro t y hy
    obtain ⟨⟨g, b, x⟩, hl, hy⟩ := K9L.ok_bind hy
    dsimp only at hy
    obtain ⟨fs, hfs, hy⟩ := K9L.ok_bind hy
    refine ⟨(g, b, x), fs, hl, named_ok hfs, ?_⟩
    rw [← Except.ok.inj hy]
    cases (names.head? == some name) <;> rfl
  have plainOk : ∀ (fs : List Kinds.Form), ∀ cl ∈ fs.map asClaim, cl.eqFirst = none := by
    intro fs cl hcl
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hcl
    rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro n t θ y y' hy hy'
    obtain ⟨z, fs, hl, hfs, rfl⟩ := cut t y hy
    obtain ⟨z', fs', hl', hfs', rfl⟩ := cut _ y' hy'
    rw [letters_re, hl] at hl'
    obtain rfl : z = z' := Except.ok.inj hl'
    obtain rfl : fs = fs' := Option.some.inj (hfs.symm.trans hfs')
    rfl
  · intro n t y hy
    obtain ⟨z, fs, hl, hfs, rfl⟩ := cut t y hy
    exact plainOk fs
  · intro n t y hy
    obtain ⟨z, fs, hl, hfs, rfl⟩ := cut t y hy
    exact ⟨rfl, rfl⟩
  · intro n t y a hy ha
    obtain ⟨z, fs, hl, hfs, rfl⟩ := cut t y hy
    exact ⟨a, ha, SameSums.refl _⟩
  · intro n t θ tl y y' hy hy'
    obtain ⟨z, fs, hl, hfs, rfl⟩ := cut t y hy
    obtain ⟨z', fs', hl', hfs', rfl⟩ := cut _ y' hy'
    unfold reBoth at hl'
    rw [letters_tl, letters_re, hl] at hl'
    obtain rfl : z = z' := Except.ok.inj hl'
    obtain rfl : fs = fs' := Option.some.inj (hfs.symm.trans hfs')
    rfl
  · intro n t y hy
    obtain ⟨z, fs, hl, hfs, rfl⟩ := cut t y hy
    exact plainOk fs
  · intro n t y hy
    obtain ⟨z, fs, hl, hfs, rfl⟩ := cut t y hy
    rfl
  · intro n t y a hy ha
    obtain ⟨z, fs, hl, hfs, rfl⟩ := cut t y hy
    exact ⟨a, ha, SameSums.refl _⟩

/-- The output head's own kind's runs. -/
theorem plain_k6 (h : Model.Head.Shape) (iU3 l piece : Nat) (p : Kinds.Head.Par) (name : String)
    (r : Nat → S → Except String (List Claim × S))
    (hr : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some r) :
    PlainRun r ∧ PlainBehind r := by
  dsimp only [kind] at hr
  exact plain_runsBy _ _ _ p h iU3 name r hr

/-! ## The merge's run -/

theorem pscRow_ok (p : Psc) (S0 : E) (kept : Aff) : FlOk (Fl.pscRow p S0 kept) :=
  FlOk.bind (FlOk.must _) fun _ => FlOk.bind (FlOk.hideRun _ _ _) fun _ => FlOk.pure _

theorem merge_cut (n : Nat) (t : S) (y : List Claim × S) (h : headMergeClaim n t = .ok y) :
    ∃ a wo x, t.here = .head a ∧ a.wo = some wo ∧ Fl.pscRow wo.p wo.fvp {} a.F [] = some x ∧
      y = ([{ form := x.1.1 }], { t with here := .head { a with F := x.2.1 } }) := by
  unfold headMergeClaim at h
  cases hh : t.here with
  | head a =>
    rw [hh] at h
    dsimp only at h
    obtain ⟨wo, hwo, h⟩ := K9L.ok_bind h
    obtain ⟨x, hx, h⟩ := K9L.ok_bind h
    exact ⟨a, wo, x, rfl, named_ok hwo, named_ok hx, (Except.ok.inj h).symm⟩
  | lay a => rw [hh] at h; cases h
  | att a => rw [hh] at h; cases h
  | between => rw [hh] at h; cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

theorem behind_merge : PlainBehind headMergeClaim := by
  constructor
  · intro n t θ tl y y' h h'
    obtain ⟨a, wo, x, ha, hwo, hx, rfl⟩ := merge_cut n t y h
    obtain ⟨a', wo', x', ha', hwo', hx', rfl⟩ := merge_cut n _ y' h'
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := t
    obtain rfl : here = .head a := ha
    obtain ⟨fr, kept, ids, Lc, F, hxx, ht, tl0, claim, wo0, Fm, slot, opened, sq, lh⟩ := a
    cases opened with
    | false =>
      obtain rfl := Here.head.inj ha'
      obtain rfl : wo = wo' := Option.some.inj (hwo.symm.trans hwo')
      obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
      rfl
    | true =>
      obtain rfl := Here.head.inj ha'
      obtain rfl : wo = wo' := Option.some.inj (hwo.symm.trans hwo')
      have e := (pscRow_ok wo.p wo.fvp {}).free F [] x θ hx
      obtain rfl : _ = x' := Option.some.inj (e.symm.trans hx')
      rfl
  · intro n t y h
    obtain ⟨a, wo, x, ha, hwo, hx, rfl⟩ := merge_cut n t y h
    intro cl hcl
    obtain rfl : cl = _ := List.mem_singleton.1 hcl
    rfl
  · intro n t y h
    obtain ⟨a, wo, x, ha, hwo, hx, rfl⟩ := merge_cut n t y h
    unfold S.tl?
    rw [ha]
  · intro n t y q h hq
    obtain ⟨a, wo, x, ha, hwo, hx, rfl⟩ := merge_cut n t y h
    have hF := K9.get_fork t q hq
    have ho : a.opened = true := by
      unfold S.fork? at hF
      rw [ha] at hF
      by_cases ho : a.opened = true
      · exact ho
      · simp [ho] at hF
    have hFa : t.fork? = some a.F := by
      unfold S.fork?
      rw [ha]
      simp [ho]
    have hput : ({ t with here := .head { a with F := x.2.1 } } : S) = t.putFork x.2.1 := by
      unfold S.putFork
      rw [ha]
      simp [ho]
    rw [hput]
    exact ledger_putFork t q a.F _ hq hFa ((pscRow_ok wo.p wo.fvp {}).same a.F [] x hx)

/-! ## The segment -/

/-- The entries of the head's segment's order in front of "K8.equations", and behind it. -/
def headPre : List (Nat × String) :=
  [(2, "objects"), (2, "guests"), (3, "norm"), (3, "join"), (3, "policy"), (2, "planes"),
    (7, "objects"), (7, "guests")]

def headPost : List (Nat × String) := [(3, "logits"), (8, "the merge")]

section
variable (L : Link S Claim) (hS : Model.Head.Shape) (iU3 l piece : Nat) (p6 : Kinds.Head.Par)
  (nU : Array Nat)
  (ties : LinkJoin.HeadTies L hS iU3 l piece p6 nU)
  (tC : ∀ run, LinkJoin.At L (2, "objects") run → LinkJoin.Under run K9.objectsCalls)
  (tD : ∀ run, LinkJoin.At L (7, "objects") run → LinkJoin.Under run K9.objectsDigits)
  (tP : ∀ run, LinkJoin.At L (2, "planes") run →
    ∃ lm, LinkJoin.Under run (K9.planesCalls lm (callerReaders (planesAt iU3))))
include ties tC tD tP

theorem head_pre : PreOk L headPre := by
  intro o ho run hat
  simp only [headPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, tC run hat, plain_objectsCalls⟩
  · exact ⟨_, ties.tGuests 2 (by simp) run hat, plain_idle⟩
  · obtain ⟨r, lr, u⟩ := ties.tK6 "norm" (by simp) run hat
    exact ⟨r, u, (plain_k6 hS iU3 l piece p6 "norm" r lr).1⟩
  · exact ⟨_, ties.tJoin run hat, plain_join _ (callerKeys_re hS iU3 p6)⟩
  · obtain ⟨r, lr, u⟩ := ties.tK6 "policy" (by simp) run hat
    exact ⟨r, u, (plain_k6 hS iU3 l piece p6 "policy" r lr).1⟩
  · obtain ⟨lm, u⟩ := tP run hat
    exact ⟨_, u, plain_planes lm _ (callerReaders_re iU3)⟩
  · exact ⟨_, tD run hat, plain_objectsDigits⟩
  · exact ⟨_, ties.tGuests 7 (by simp) run hat, plain_idle⟩

omit tC tD tP in
theorem head_post : PostOk L headPost := by
  intro o ho run hat
  simp only [headPost, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · obtain ⟨r, lr, u⟩ := ties.tK6 "logits" (by simp) run hat
    exact ⟨r, u, (plain_k6 hS iU3 l piece p6 "logits" r lr).2⟩
  · exact ⟨_, ties.tMerge run hat, behind_merge⟩

/-- **`Gathers` at the head's segment.** -/
theorem gathers_head (p : K9.Where) (s : S) (tl : HTailF2) (funs : Array HFun)
    (hord : L.order = orderOf .head) (ht : s.tl? = some tl) (hf : s.funs? = some funs) :
    ∃ (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E),
      Gathers p (claimsInBy L.each L.hear L.order) s tl funs nf nb a :=
  gathers_of_plain L p 5 headPre headPost (by rw [hord]; rfl)
    (head_pre L hS iU3 l piece p6 nU ties tC tD tP) (head_post L hS iU3 l piece p6 nU ties) ties.tEq
    s tl funs ht hf

/-- **The count at the head's segment's batching.** -/
theorem fall_few_head (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s : S)
    (tU d : Nat) (hord : L.order = orderOf .head)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (hU : ∀ tl, s.tl? = some tl → unitsLaid nU tl tU = true)
    (hd : ∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
      F.planClaimsF + topOf tl funs ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch (zeroUnitAt nU) s [chiAt x] = true) ≤
      nU.getD 2 0 * d :=
  fall_few_any p _ batch nU s tU d
    (fun tl funs ht hf =>
      gathers_head L hS iU3 l piece p6 nU ties tC tD tP p s tl funs hord ht hf)
    (fun dr t e cls hdr hg => funs_of_yes L p 5 headPre headPost (by rw [hord]; rfl)
      (head_pre L hS iU3 l piece p6 nU ties tC tD tP) (head_post L hS iU3 l piece p6 nU ties)
      ties.tEq s dr t e cls hdr hg)
    hb hU hd

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.letters_re
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_runsBy
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_merge
#print axioms VerifiableInference.Desc.First.K8.Honest.gathers_head
#print axioms VerifiableInference.Desc.First.K8.Honest.fall_few_head
