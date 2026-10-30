-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsPend.lean: a property of what the view's rounds that are not yet closed
have drawn, each against its entry of the plan: from the strict reader, along every routine that
keeps, to every context of the run of an accepted proof file. One general form, and two values of
it.

Definitions, statements and proofs. NzStart.lean and two files that are not in this library do this
for the property `NzCtx` (OnBytes/Tie/Pv/Psc/Run/NzCtx.lean). Nothing in their proofs hangs on what
is asked of an entry and a round's draws. Here that is a letter Q.
Main names:
  `PendAll Q c`: a run on a view, and Q holds of the k-th unused entry of the plan and of what the
    k-th round that is not yet closed has drawn, for every k.
  `nzCtx_iff`: `NzCtx ρ` is `PendAll (NzAt ρ)`, by definition.
  `pend_of_kept`: `PendAll Q` goes along Kept. `keeps_pend`, `runs_pend`: so along every block with
    Keeps and every routine with KeepsM.
  `step_pend`, `chain_pend`, `fileRan_pend`: along one call of runLinkH, along the calls over a
    list of links, and along the first chain's block.
  `readIn_pend`, `pend_start`: if Q holds of every entry and of what the format's rule draws at it
    in the second field, `PendAll Q` holds at the context from which the first chain's block is
    run on the view of a proof file that was read.
  `OkAt`, `OkCtx`: the value "every drawn element has words below the prime".
  `drawElems_ok`, `drawRound_ok`, `okCtx_start`: it holds at the start.
  `closeOne_ok`, `hearOne_ok`: the element that a closing hands out from a context with `OkCtx` has
    words below the prime.
  `gl_of_ok`: an element with words below the prime that is not the word 0 does not read as 0 in the
    library's field.
Limits: the second field alone at the start. The first chain alone. Hypothesis along the links:
every link's routine keeps.
-/
import OnBytes.Slice.ProgField
import OnBytes.Tie.Pv.Keeps.KeepsCut
import OnBytes.Tie.Pv.Keeps.NzStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Pend

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5

/-- A run on a view, and Q holds of the k-th unused entry and the k-th round not yet closed. -/
def PendAll (Q : Fmt.Entry → Fmt.Drawn → Prop) (c : Ctx) : Prop :=
  c.ch.dry = false ∧ ∀ (k : Nat) (e : Fmt.Entry) (r : Fmt.RoundView), c.ch.entries[k]? = some e →
    c.ch.pending[k]? = some r → Q e r.drawn

theorem nzCtx_iff {K : Type} [CommRing K] (ρ : Reading K) (c : Ctx) :
    Road.NzCtx ρ c ↔ PendAll (Road.NzAt ρ) c := Iff.rfl

variable {Q : Fmt.Entry → Fmt.Drawn → Prop}

/-- `PendAll Q` goes along Kept. -/
theorem pend_of_kept {c c' : Ctx} (h : PendAll Q c) (k : Kept c c') : PendAll Q c' := by
  obtain ⟨n, e1, p1⟩ := k.tail h.1
  refine ⟨k.dry.trans h.1, fun j e r he hr => ?_⟩
  rw [e1, List.getElem?_drop] at he
  have h1 : (c'.ch.pending.map (·.drawn))[j]? = some r.drawn := by
    rw [List.getElem?_map, hr]
    rfl
  rw [p1, List.getElem?_map, List.getElem?_drop] at h1
  obtain ⟨r0, hr0, e0⟩ := Option.map_eq_some_iff.1 h1
  have h2 := h.2 (n + j) e r0 he hr0
  rw [show r0.drawn = r.drawn from e0] at h2
  exact h2

theorem keeps_pend {α : Type} (b : Blk α) [k : L5.Keeps b] {c : Ctx} {a : α} {c' : Ctx}
    (h : PendAll Q c) (y : b c = .ok (a, c')) : PendAll Q c' := pend_of_kept h (k.out c a c' y)

theorem runs_pend {m : Type → Type} [Monad m] [HasKeeps m] [HasRuns m] [RunsKeep m] {α : Type}
    {x : m α} [k : KeepsM x] {s : HasRuns.St m} {a : α} {s' : HasRuns.St m} (h : Runs x s a s')
    (d : PendAll Q (HasRuns.ctx s)) : PendAll Q (HasRuns.ctx s') :=
  pend_of_kept d (RunsKeep.kept k.out h)

/-- One call of runLinkH. -/
theorem step_pend {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx} {l : Nat}
    {X : LinkH} [KeepsM X.run] {check : ChainCheck} {out : Proof.LinksResult} {c : Ctx}
    {r : ChainCheck × Proof.LinksResult} {c' : Ctx} {chk : ChainCheck} {o : Option WsForkOut}
    {C' : LinkCtx} {F' : Fork} {c1 c2 : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2) (h : PendAll Q c) :
    PendAll Q c1 ∧ PendAll Q c2 ∧ PendAll Q c' := by
  obtain ⟨q1, q2, q3⟩ := Cut.kept_parts S
  exact ⟨pend_of_kept h q1, pend_of_kept h (q1.trans q2), pend_of_kept h ((q1.trans q2).trans q3)⟩

/-- The calls of runLinkH over a list of links. -/
theorem chain_pend {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx}
    {rest : List LinkH} (hk : ∀ X ∈ rest, KeepsM X.run) {l : Nat} {check : ChainCheck}
    {out : Proof.LinksResult} {c : Ctx} {r : ChainCheck × Proof.LinksResult} {c' : Ctx}
    (A : LinksChain links p wsLay cEnd rest l check out c r c') (h : PendAll Q c) : PendAll Q c' :=
  pend_of_kept h (Reply.kept_chain hk A)

/-- The first chain's block, whole. -/
theorem fileRan_pend {Z : Array LinkH} (hk : AllKeep Z) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay}
    {file : ByteArray} {r : Proof.ProofRead} {fin : Proof.FirstEnd} {cE : Ctx}
    {check0 : ChainCheck} {ca : Ctx} {rN : ChainCheck × Proof.LinksResult} {cb cc : Ctx}
    {lin : LinFirst} {cd : Ctx}
    (R : FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd)
    (h : PendAll Q (startOf (Proof.firstStart c.first) r.first.view)) :
    PendAll Q ca ∧ PendAll Q cb ∧ PendAll Q cc ∧ PendAll Q cd ∧ PendAll Q cE := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := Cut.fileRan_kept hk R
  have ha := pend_of_kept h k1
  have hb := pend_of_kept ha k2
  have hc := pend_of_kept hb k3
  have hd := pend_of_kept hc k4
  exact ⟨ha, hb, hc, hd, pend_of_kept hd k5⟩

/-! ## The start -/

/-- A chain that was read: the k-th round of its view against the k-th entry of the plan. -/
theorem readIn_pend (hQ : ∀ e k row, Q e (Fmt.drawRound .two e k row)) (S : Fmt.SpecX)
    (hf : S.base.plan.field = .two) (b : ByteArray) (i : Nat) (s s' : Session) (cr : ChainRead)
    (h : readIn S b i s = some (cr, s')) (k : Nat) (e : Fmt.Entry) (r : Fmt.RoundView)
    (he : S.base.plan.rounds[k]? = some e) (hr : cr.view.rounds[k]? = some r) : Q e r.drawn := by
  unfold readIn at h
  split at h
  · cases h
  · rename_i o j hq
    cases h
    rw [readChain_eq] at hq
    obtain ⟨hok, hall⟩ := Nz.readChainX_out Fmt.formatHash S s.seen b i o j hq
    have hent : S.base.rounds.map (·.entry) = S.base.plan.rounds := by
      have h1 := hok
      simp only [Fmt.SpecX.ok, Fmt.Spec.ok, Bool.and_eq_true, beq_iff_eq] at h1
      tauto
    have hr' : (Fmt.viewX S o).rounds[k]? = some r := by
      rw [← viewOf_eq]
      exact hr
    have hr2 : (o.rounds.toList.map fun x : Fmt.RoundOut =>
        (⟨Fmt.noRoots x.vals, x.drawn⟩ : Fmt.RoundView))[k]? = some r := hr'
    rw [List.getElem?_map] at hr2
    obtain ⟨ro, hro, rfl⟩ := Option.map_eq_some_iff.1 hr2
    obtain ⟨x, hx, row, hd⟩ := Nz.forall2_get hall k ro hro
    have hx1 : S.base.rounds[k]? = some x.1 := (List.getElem?_zip_eq_some.1 hx).1
    have he' : x.1.entry = e := by
      rw [← hent, List.getElem?_map, hx1] at he
      exact Option.some.inj he
    show Q e ro.drawn
    rw [hd, hf, he']
    exact hQ e x.1.kind row

/-- `PendAll Q` at the context from which the first chain's block is run on the view of a proof file
that was read. -/
theorem pend_start (hQ : ∀ e k row, Q e (Fmt.drawRound .two e k row)) (c : Params.ProofChains)
    (table : Params.TableName) (copy : Nat) (request words : ByteArray) (block : Blk Proof.FirstEnd)
    (file : ByteArray) (r : Proof.ProofRead)
    (h : (Proof.readProof c table copy request words block file).fromStart = .ok r) :
    PendAll Q (startOf (Proof.firstStart c.first) r.first.view) := by
  obtain ⟨hf, rs, S, i, s, s', hS, hr⟩ :=
    Nz.readProof_first c table copy request words block file r h
  have hp := Nz.describe_plan c.first table copy request words rs S hS
  refine ⟨rfl, fun k e rv he hv => ?_⟩
  exact readIn_pend hQ S (by rw [hp]; exact hf) file i s s' r.first hr k e rv
    (by rw [hp]; exact he) hv

/-! ## Every drawn element has words below the prime -/

/-- Every drawn element has words below the prime of the second field. -/
def OkAt (_ : Fmt.Entry) (d : Fmt.Drawn) : Prop := ∀ x ∈ d.elems, Fmt.Fld.two.okE x = true

/-- The same of all rounds that are not yet closed. -/
def OkCtx (c : Ctx) : Prop := PendAll OkAt c

open Fmt in
theorem drawSeedL_ok (v : Nat) (row : Fmt.Row) (c : Nat) :
    ∀ x ∈ (drawSeedL .two v row c).1, Fld.two.okE x = true := by
  intro x hx
  have hx' : x ∈ (((drawE .two).times v) row c).1 ++
      [(drawNZ .two row (((drawE .two).times v) row c).2).1] := hx
  rcases List.mem_append.1 hx' with h | h
  · exact Nz.times_each (drawE .two) (fun y => Fld.two.okE y = true) row (Nz.drawE_ok row) v c x h
  · rw [List.mem_singleton.1 h]
    exact (Nz.drawNZ_good row _).1

open Fmt in
theorem drawElems_ok (e : Fmt.Entry) (k : Fmt.Kind) (row : Fmt.Row) (c : Nat) :
    ∀ x ∈ (drawElems .two e k row c).1, Fld.two.okE x = true := by
  unfold drawElems
  split
  · intro x hx
    have hx' : x ∈
        (((drawSeedL .two ((e.drawE - e.drawNZ) / e.drawNZ)).times e.drawNZ) row c).1.flatten
        ++ (((drawE .two).times ((e.drawE - e.drawNZ) % e.drawNZ)) row
          (((drawSeedL .two ((e.drawE - e.drawNZ) / e.drawNZ)).times e.drawNZ) row c).2).1 := hx
    rcases List.mem_append.1 hx' with h | h
    · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 h
      exact Nz.times_each (drawSeedL .two _) (fun l => ∀ y ∈ l, Fld.two.okE y = true) row
        (drawSeedL_ok _ row) _ c l hl x hxl
    · exact Nz.times_each (drawE .two) (fun y => Fld.two.okE y = true) row (Nz.drawE_ok row) _ _ x h
  · intro x hx
    have hx' : x ∈ (((drawE .two).times (e.drawE - e.drawNZ)) row c).1 ++
        (((drawNZ .two).times e.drawNZ) row
          (((drawE .two).times (e.drawE - e.drawNZ)) row c).2).1 := hx
    rcases List.mem_append.1 hx' with h | h
    · exact Nz.times_each (drawE .two) (fun y => Fld.two.okE y = true) row (Nz.drawE_ok row) _ _ x h
    · exact Nz.times_each (drawNZ .two) (fun y => Fld.two.okE y = true) row
        (fun c' => (Nz.drawNZ_good row c').1) _ _ x h

theorem drawRound_ok (e : Fmt.Entry) (k : Fmt.Kind) (row : Fmt.Row) :
    OkAt e (Fmt.drawRound .two e k row) := drawElems_ok e k row _

/-- `OkCtx` at the start. -/
theorem okCtx_start (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk Proof.FirstEnd) (file : ByteArray)
    (r : Proof.ProofRead)
    (h : (Proof.readProof c table copy request words block file).fromStart = .ok r) :
    OkCtx (startOf (Proof.firstStart c.first) r.first.view) :=
  pend_start drawRound_ok c table copy request words block file r h

/-- The element that a closing hands out. -/
theorem closeOne_ok (name : String) (kind : Fmt.Kind) (nz : Nat) (x : E) (c c' : Ctx) (h : OkCtx c)
    (y : (Blk.closeOne name kind nz).Yields c x c') : okE x = true := by
  obtain ⟨d, y1, hd⟩ := Blk.closeOne_inv name kind nz x c c' y
  obtain ⟨e, es, r, rest, a1, _, _, a4, _, a6, _⟩ := Blk.close_inv name kind nz d c c' h.1 y1
  have hn := h.2 0 e r (by rw [a1]; rfl) (by rw [a4]; rfl) x.triple (by rw [← a6, hd]; simp)
  rw [okE_triple]
  exact hn

/-- The same for a message and its closing. -/
theorem hearOne_ok (name : String) (kind : Fmt.Kind) (n nz : Nat) (q : List E) (x : E)
    (c c' : Ctx) (h : OkCtx c) (y : (OnBytes.Psc.hearOne name kind n nz).Yields c (q, x) c') :
    okE x = true := by
  unfold OnBytes.Psc.hearOne at y
  obtain ⟨q', c1, y1, y2⟩ := (Blk.yields_bind _ _ _ _ _).1 y
  obtain ⟨g, c2, y3, y4⟩ := (Blk.yields_bind _ _ _ _ _).1 y2
  obtain ⟨e1, _⟩ := (Blk.yields_pure _ _ _ _).1 y4
  have e2 : x = g := congrArg Prod.snd e1
  rw [e2]
  exact closeOne_ok name kind nz g c1 c2
    (keeps_pend (Blk.recvEs n) h ((Blk.yields_iff _ _ _ _).1 y1)) y3

/-- Words below the prime, and not the word 0: it does not read as 0 in the library's field. -/
theorem gl_of_ok (x : E) (hok : okE x = true) (hz : isZeroE x = false) :
    Reading.gl.val x ≠ 0 := fun h0 => by
  have h1 : isZeroE x = true := (Slice.isZeroE_iff x hok).2 h0
  rw [hz] at h1
  cases h1

end OnBytes.Tie.Pv.Keeps.Pend

#print axioms OnBytes.Tie.Pv.Keeps.Pend.pend_of_kept
#print axioms OnBytes.Tie.Pv.Keeps.Pend.fileRan_pend
#print axioms OnBytes.Tie.Pv.Keeps.Pend.pend_start
#print axioms OnBytes.Tie.Pv.Keeps.Pend.okCtx_start
#print axioms OnBytes.Tie.Pv.Keeps.Pend.closeOne_ok
#print axioms OnBytes.Tie.Pv.Keeps.Pend.hearOne_ok
#print axioms OnBytes.Tie.Pv.Keeps.Pend.gl_of_ok
