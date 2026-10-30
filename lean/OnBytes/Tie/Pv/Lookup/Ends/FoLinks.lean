-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLinks.lean.
From the start of a proof's links to every sub-proof's routine: each routine starts on the view with
no message open.

`link_entry` (OnBytes/Tie/Pv/Lookup/Ends/FoSiteFirst.lean) leaves one premise: that the run is on a
view where `runLinkH`
begins. Here that premise is carried from the first link to every later one.

 * `Dry.inPlace`: a block that is run under the name of a place.
 * `dry_runLinkH`: one link stays on the view, if its sub-proof's routine does.
 * `LinksRan links p wsLay rest l check out c r`: a proposition by recursion on the links that are
   still to come. For the first of them it holds `link_entry`'s three facts from (check, c), and the
   run of `runLinkH` from (check, out, c) to (check1, out1, c3); for the others the same from
   (check1, out1, c3). Behind the last, r is what is left. So each link's start is the end of the
   link before, and every witness is fixed by a run equation whose start is named.
 * `links_ran`: if the links that are still to come run from a context on a view and return r, and
   each link's routine stays on the view, then `LinksRan`.
 * `run_ran`: all links of a proof (`runLinksH`): the start of the chain's calls from c itself,
   `LinksRan` behind it, and the chain's last call to the context of the result.
 * `staysL_some`, `staysL_none`: the forms in which the three kinds of sub-proof are handed to a
   link: with OnBytes/Tie/Pv/Lookup/Ends/FoStaysTop.lean each of them stays on the view.

A premise is left: that the run is on a view where `runLinksH` begins.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysTop

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem Dry.inPlace {α : Type} {b : Blk α} (h : Dry b) (place : String) :
    Dry (Blk.inPlace place b) :=
  ⟨fun c a c' e hd => h.out c a c' (inPlace_ok _ _ _ _ e) hd⟩

theorem dry_runLinkH (links : Array Stages.LinkH) (p : Params.First) (wsLay : WsLay) (l : Nat)
    (X : Stages.LinkH) (check : ChainCheck) (out : Proof.LinksResult) (hX : DryL X.run) :
    Dry (Stages.runLinkH links p wsLay l X check out) := by
  have h1 : ∀ C : LinkCtx, Dry (Blk.inPlace X.name ((StateT.run X.run C).run X.Fp)) :=
    fun C => Dry.inPlace (hX C X.Fp) _
  unfold Stages.runLinkH
  stays

/-- The links that are still to come have run, one after the other: each link's first call of the
chain from the context in which the link before ended; behind it no message is open; there the
link's routine, from the link's state made of that call's result and from the planned state. r: what
the last link leaves. -/
def LinksRan (links : Array Stages.LinkH) (p : Params.First) (wsLay : WsLay) :
    List Stages.LinkH → Nat → ChainCheck → Proof.LinksResult → Ctx →
      (ChainCheck × Proof.LinksResult) × Ctx → Prop
  | [], _, check, out, c, r => r = ((check, out), c)
  | X :: rest, l, check, out, c, r =>
    ∃ (check' : ChainCheck) (c1 c2 : Ctx) (o : Option WsForkOut) (C : LinkCtx) (F : Fork)
      (check1 : ChainCheck) (out1 : Proof.LinksResult) (c3 : Ctx),
      check.first c = .ok (check', c1) ∧ Clean c1 ∧
      X.run { check := check', link := l, arrayOf := X.arrayOf, list := X.Tp } X.Fp c1 =
        .ok (((o, C), F), c2) ∧
      Stages.runLinkH links p wsLay l X check out c = .ok ((check1, out1), c3) ∧
      LinksRan links p wsLay rest (l + 1) check1 out1 c3 r

theorem links_ran (links : Array Stages.LinkH) (p : Params.First) (wsLay : WsLay) :
    ∀ (rest : List Stages.LinkH) (l : Nat) (check : ChainCheck) (out : Proof.LinksResult)
      (c : Ctx) (r : (ChainCheck × Proof.LinksResult) × Ctx),
      (∀ X ∈ rest, DryL X.run) →
      Stages.runLinksFrom links p wsLay rest l check out c = .ok r → c.ch.dry = false →
      LinksRan links p wsLay rest l check out c r
  | [], _, check, out, c, r, _, h, _ => by
    rw [Stages.runLinksFrom] at h
    exact (pureB_ok _ _ _).1 h
  | Y :: rest, l, check, out, c, r, hY, h, hd => by
    rw [Stages.runLinksFrom] at h
    obtain ⟨⟨check1, out1⟩, c3, h1, h2⟩ := (bindB_ok _ _ _ _).1 h
    obtain ⟨k, d1, d2, o, C, F, e0, e1, e2⟩ := link_entry links p wsLay l Y check out c _ h1 hd
    have hd3 : c3.ch.dry = false :=
      (dry_runLinkH links p wsLay l Y check out (hY Y (by simp))).out c _ c3 h1 hd
    exact ⟨k, d1, d2, o, C, F, check1, out1, c3, e0, e1, e2, h1,
      links_ran links p wsLay rest (l + 1) check1 out1 c3 r
        (fun Z hZ => hY Z (List.mem_cons_of_mem _ hZ)) h2 hd3⟩

theorem dry_checkStart (shape : Params.ReqShape) (layout : Params.ReqLayout) :
    Dry (ChainCheck.start shape layout) := by stays

/-- All links of a proof: the start of the chain's calls from c itself, then the links. -/
theorem run_ran (links : Array Stages.LinkH) (p : Params.First) (wsLay : WsLay) (c : Ctx)
    (r : Proof.LinksResult × Ctx) (hY : ∀ X ∈ links.toList, DryL X.run)
    (h : Stages.runLinksH links p wsLay c = .ok r) (hd : c.ch.dry = false) :
    ∃ (check check2 : ChainCheck) (c1 c2 : Ctx),
      ChainCheck.start p.shape p.layout c = .ok (check, c1) ∧
      LinksRan links p wsLay links.toList 0 check {} c1 ((check2, r.1), c2) ∧
      check2.finish c2 = .ok ((), r.2) := by
  unfold Stages.runLinksH at h
  obtain ⟨check, c1, h1, h⟩ := (bindB_ok _ _ _ _).1 h
  obtain ⟨⟨check2, out2⟩, c2, h2, h⟩ := (bindB_ok _ _ _ _).1 h
  obtain ⟨_, c3, h3, h⟩ := (bindB_ok _ _ _ _).1 h
  cases (pureB_ok _ _ _).1 h
  exact ⟨check, check2, c1, c2, h1,
    links_ran links p wsLay links.toList 0 check {} c1 _ hY h2
      ((dry_checkStart _ _).out c _ c1 h1 hd), h3⟩

/-- A routine whose value is handed on under `some`. -/
theorem staysL_some {α : Type} {x : LinkM α} (h : DryL x) : DryL (some <$> x) := h.map _

/-- A routine behind which `none` is handed on. -/
theorem staysL_none {α β : Type} {x : LinkM α} (h : DryL x) :
    DryL (x >>= fun _ => (pure none : LinkM (Option β))) := h.bind fun _ => DryL.pure _

end Fo
