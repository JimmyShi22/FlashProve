-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GroupRest.lean: WHERE A LINK IS OPEN, ITS FRAME's GROUP NUMBER IS
THE LINK's NUMBER: PART TWO: THE LINKS 0 TO 23, FROM BEHIND THE BATCHING TO IN FRONT OF "cleared"
(the cuts 14 l + 10 to 14 l + 14): so in front of the one equation and of the closing.
  link_putLink, link_putFork, gk_set: what kind K9's lens writes.
  drawn_link; batch_gk, oneEquation_gk, closing_gk, shut_gk, closeOf_gk: Gk
    (Johnson/IMR/GroupAt.lean) at
    kind K9's and K10's makers: the batching's draw leaves the open link's state of the calls and
    its number; the one equation leaves the link's context whole; the closing writes the frame's
    carried rows, mask, link and "next", not its group (kind K10's closeFrame_lays); the
    shutting lays the same frame back.
  group_open: BOTH PARTS IN ONE: at every cut 14 l + 3 + n, n ≤ 11. fold_cut: a tool.
NOT HERE YET: the head's link.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: the list of facts along the fold,
field "groupIs"; the link's law's files (the one equation; the closing).
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupAt
import Johnson.IMR.LinkRest
import Johnson.Goal.Meaning.GroupCalmK9
import Johnson.Desc.First.Close.Law.Lays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9
open ProofFile (Cl)

theorem link_putLink {s : S} {L : LinkCtx} (h : s.link? = some L) (L' : LinkCtx) :
    (s.putLink L').link? = some L' := by
  unfold S.link? at h
  unfold S.putLink S.link?
  cases hs : s.here with
  | lay a => simp
  | att a => simp
  | head a =>
    rw [hs] at h
    by_cases ho : a.opened = true
    · simp [ho]
    · simp [ho] at h
  | between => rw [hs] at h; cases h
  | fin a => rw [hs] at h; cases h
  | mem a => rw [hs] at h; cases h

theorem link_putFork (s : S) (F : Fork) : (s.putFork F).link? = s.link? := by
  unfold S.putFork S.link?
  cases hs : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho, hs]
  | _ => simp [hs]

theorem gk_set {s : S} {L : LinkCtx} (h : s.link? = some L) (p : K9.Part)
    (e1 : p.L.check.frame.group = L.check.frame.group) (e2 : p.L.link = L.link) :
    Gk s (atS.set s p) := fun L₀ h₀ => by
  obtain rfl : L = L₀ := Option.some.inj (h.symm.trans h₀)
  refine ⟨p.L, ?_, e1, e2⟩
  show ((s.putLink p.L).putFork p.F).link? = _
  rw [link_putFork, link_putLink h]

theorem drawn_link {rows : Nat} {chi : E} {owed : RowsOwed} {used : Nat} {L : LinkCtx} {F : Fork}
    {o : Drawn} (h : drawnClean rows chi owed used L F = .ok o) : o.L.link = L.link := by
  unfold drawnClean at h
  obtain ⟨o', h1, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  unfold drawn at h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  cases h1
  rfl

/-- **The batching.** -/
theorem batch_gk (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl Gk claims) : Decides Gk (batch atS p claims) := by
  intro s rs gs s' h
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : Gk s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      exact gk_set (atS_get (there_some hq)).1 _
        (by show o.L.check.frame.group = _; rw [drawn_L ho]) (drawn_link ho)
    · cases h1
  have a2 : Gk t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    exact gk_trans _ _ _ (hcl t₁ x hx) (gk_set (atS_get (there_some hq)).1 _ rfl rfl)
  exact gk_trans _ _ _ a1 a2

/-- **The one equation.** -/
theorem oneEquation_gk {C : Type} (p : Where) : Decides Gk (oneEquation (Cl := C) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  obtain ⟨d1, -⟩ := door_keeps ho
  exact gk_set (atS_get (there_some hq)).1 _ (by show o.L.check.frame.group = _; rw [d1])
    (by show o.L.link = _; rw [d1])

/-- **The closing.** -/
theorem closing_gk {C : Type} (P : Close.Par) : Decides Gk (K9.closing (Cl := C) P) := by
  intro s rs gs s' h L hL
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  obtain ⟨G, rows, -, -, e⟩ := Close.closeFrame_lays (f' := x.1) (S' := x.2) hx
  refine ⟨{ L with check := { s.live with frame := x.1 } }, ?_, ?_, rfl⟩
  · show (s.putLive { s.live with frame := x.1 }).link? = _
    unfold S.putLive
    rw [hL]
    exact link_putLink hL _
  · show x.1.group = _
    rw [e]
    show s.live.frame.group = _
    rw [live_open hL]

/-- **The shutting.** -/
theorem shut_gk {C : Type} (p : Where) (piece : Nat) : Decides Gk (K9.shut (Cl := C) p piece) := by
  intro s rs gs s' h L hL
  obtain ⟨L₁, h1, h⟩ := bindE h
  cases h
  obtain rfl : L = L₁ := by
    rw [hL] at h1
    exact Except.ok.inj h1
  exact ⟨_, link_putLink hL _, rfl, rfl⟩

theorem closeOf_gk (p : Where) (P : Close.Par) :
    ∀ b ∈ closeOf (Cl := Unit) p P, Decides Gk b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact fun s rs gs t h => oneEquation_gk (C := Unit) p s rs gs t h
  · exact closing_gk P
  · exact shut_gk p _

/-- A fold over a longer front part of a list gives one over every shorter. -/
theorem fold_cut {ft : Nat} {bs : List (Block S Cl)} {s : S} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn} {k : Nat} :
    ∀ (d : Nat) {t' : S} {r' : List Fmt.RoundView} {c' : List VerifiableInference.Desc.OpenedColumn},
      foldBlocks ft (bs.take (k + d)) s rs cols = .ok (t', r', c') →
      ∃ t r c, foldBlocks ft (bs.take k) s rs cols = .ok (t, r, c)
  | 0, t', r', c', h => ⟨t', r', c', h⟩
  | d + 1, _, _, _, h => by
    obtain ⟨t, r, c, h'⟩ := fold_back (k := k + d) h
    exact fold_cut d h'

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY LINK l < 24, AT THE STATE BEHIND THE FIRST 14 l + 3 + n ENTRIES OF THE FLAT LIST,
n ≤ 11 (from behind the link's first sub-protocol to in front of "cleared"): A LINK IS OPEN, WITH
THE NUMBER l, AND ITS FRAME BEARS THE GROUP l.** -/
theorem group_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 11, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      ∃ L, t.link? = some L ∧ L.link = l ∧ L.check.frame.group = l
  | 0, _, t, R', C', f => group_at hS hR O hl 0 (by omega) t R' C' f
  | n + 1, hn, t, R', C', f => by
    by_cases h6 : n + 1 ≤ 6
    · exact group_at hS hR O hl (n + 1) h6 t R' C' f
    · obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + 3 + n) f
      obtain ⟨L, hL, e1, e2⟩ := group_open hS hR O hl n (by omega) u Ru Cu fu
      obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
      obtain ⟨Lk, -, -, -, bC, eL, hlen, -, -, -, -, -, -, -, -, -, -, -, iC, -⟩ := hfr l (by omega)
      rw [if_neg (by omega : ¬ l = 24)] at hlen
      rw [hlen] at iC
      obtain ⟨b, ib⟩ : ∃ b, c.blocksInOrder[14 * l + 3 + n]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by
          have := (List.getElem?_eq_some_iff.1 iC).1
          omega)⟩
      obtain ⟨rs, gs, d⟩ := fold_next ib fu f
      have hy : ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t := by
        intro b₀ e0
        have i0 : c.blocksInOrder[14 * l + 2]? = some b₀ := by
          have q := IM.hear_at_flat eL e0
          rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
            (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at q
        obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) n fu
        obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
        obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
        exact ⟨_, _, _, _, d0⟩
      have ib' : c.blocksInOrder[14 * l + 9 + (n - 6)]? = some b := by
        rw [show 14 * l + 9 + (n - 6) = 14 * l + 3 + n by omega]
        exact ib
      obtain ⟨L', hL', g1, g2⟩ := rest_by gk_refl gk_trans (fun _ _ => gk_of_quiet)
        (fun p _ hcl => batch_gk p hcl) closeOf_gk hS hR O hl eL hy (by omega) ib' u rs gs t d L hL
      exact ⟨L', hL', g2.trans e1, g1.trans e2⟩

end

#print axioms batch_gk
#print axioms closeOf_gk
#print axioms group_open

end Meaning.K2
