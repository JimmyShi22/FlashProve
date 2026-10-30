-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallLayersAny.lean: `Gathers` AT A FEED-FORWARD SEGMENT's FUNCTION OF CLAIMS, AT EVERY
STATE: THAT THE STATE STANDS IN A FEED-FORWARD SEGMENT COMES OUT OF A YES TOO. Statements and proofs. No
prover.

The run "front" returns only at a state that stands in a feed-forward segment (the library's equation
frontAtC); the runs in front of it and the draw lay a ledger and a link's context, which keeps the sort
of segment both ways. So where the function of claims returns behind some draw, the state in front of
the draw stood in a feed-forward segment; where it returns behind none, `Gathers` asks nothing.
  `here_of_putFork`, `here_of_putLink`, `here_of_set`   the sort of segment, backwards
  `layers_here`   one yes: the state in front of the draw stands in a feed-forward segment
  **`gathers_layers_any`**   from the ties and the order alone: at every state s that holds the smallness
      test's data tl and the list of tables funs: `Gathers` at tl and funs, at SOME numbers and
      coefficients
  **`fall_few_layers`**   so the count of Johnson/Desc/K8/Honest/FallCount.lean at a feed-forward segment's
      batching, with no premise on the runs and none that something is there in the state: whatever
      data the state holds pass `unitsLaid`, and d bounds the exponents at whatever it holds
Limits: the ties are premises.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallLayersLaw
import Johnson.Desc.K8.Honest.FallFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open OnBytes.Desc.First.K4 (frontAtC)
open OnBytes.Tie.Pv.Tail.Port (topOf)

theorem here_of_putFork {t : S} {G : Fork} {A : LayOwn} (h : (t.putFork G).here = .lay A) :
    ∃ A', t.here = .lay A' := by
  cases hh : t.here with
  | lay a => exact ⟨a, rfl⟩
  | att a => simp [S.putFork, hh] at h
  | head a => by_cases ho : a.opened = true <;> simp [S.putFork, hh, ho] at h
  | between => simp [S.putFork, hh] at h
  | fin a => simp [S.putFork, hh] at h
  | mem a => simp [S.putFork, hh] at h

theorem here_of_putLink {t : S} {Lc : LinkCtx} {A : LayOwn} (h : (t.putLink Lc).here = .lay A) :
    ∃ A', t.here = .lay A' := by
  cases hh : t.here with
  | lay a => exact ⟨a, rfl⟩
  | att a => simp [S.putLink, hh] at h
  | head a => by_cases ho : a.opened = true <;> simp [S.putLink, hh, ho] at h
  | between => simp [S.putLink, hh] at h
  | fin a => simp [S.putLink, hh] at h
  | mem a => simp [S.putLink, hh] at h

theorem here_of_set {s : S} {q : K9.Part} {A : LayOwn} (h : (K9.atS.set s q).here = .lay A) :
    ∃ a₀, s.here = .lay a₀ := by
  have h' : ((s.putLink q.L).putFork q.F).here = .lay A := h
  obtain ⟨A1, h1⟩ := here_of_putFork h'
  exact here_of_putLink h1

/-- One yes of the function of claims behind a draw: the state in front of the draw stands in a
feed-forward segment. -/
theorem layers_here (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (p : K9.Where) (s : S) (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (hord : L.order = orderOf .layers) (d : Fmt.Drawn) (t e : S) (cls : List Claim)
    (hdr : drawnAt p s d = .ok t) (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) :
    ∃ a₀, s.here = .lay a₀ := by
  obtain ⟨a0, x0, dr, -, -, -, htt⟩ := drawnAt_ok p s t d hdr
  rw [hord, claimsInBy_eq] at hg
  have ho7 : orderOf .layers = [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"),
      (6, "guests"), (4, "K8.equations"), (2, "back")] := rfl
  rw [ho7] at hg
  simp only [runAll] at hg
  obtain ⟨z1, g1, hg⟩ := bind_ok hg
  obtain ⟨z2, g2, hg⟩ := bind_ok hg
  obtain ⟨z3, g3, -⟩ := bind_ok hg
  obtain ⟨r1, c1, e1, at1, y1, rfl⟩ := step_ok g1
  obtain ⟨F1, gC, -, -, rfl, rfl⟩ := objectsBy_ok _ _ _ _ _ (tC r1 at1 _ _ _ _ y1)
  obtain ⟨r2, c2, e2, at2, y2, rfl⟩ := step_ok g2
  have i2 := Except.ok.inj (ties.tGuests 1 (by simp) r2 at2 _ _ _ _ y2)
  obtain rfl : [] = c2 := congrArg Prod.fst i2
  obtain rfl : _ = e2 := congrArg Prod.snd i2
  obtain ⟨r3, c3, e3, at3, y3, rfl⟩ := step_ok g3
  obtain ⟨q3, l3, u3⟩ := ties.tFront r3 at3
  obtain ⟨A3, o, fs3, G3, -, -, -, w3⟩ := frontAtC l3 (u3 _ _ _ _ y3)
  obtain ⟨A1, h1⟩ := here_of_putFork (wrote_here w3).1
  rw [htt] at h1
  exact here_of_set h1

/-- **At every state.** -/
theorem gathers_layers_any (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (p : K9.Where) (s : S) (tl : HTailF2) (funs : Array HFun)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = orderOf .layers) (ht : s.tl? = some tl) (hf : s.funs? = some funs) :
    ∃ (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E),
      Gathers p (claimsInBy L.each L.hear L.order) s tl funs nf nb a := by
  by_cases hyes : ∃ (d : Fmt.Drawn) (t e : S) (cls : List Claim), drawnAt p s d = .ok t ∧
      claimsInBy L.each L.hear L.order t = .ok (cls, e)
  · obtain ⟨d, t, e, cls, hdr, hg⟩ := hyes
    obtain ⟨a₀, hs⟩ := layers_here L p4 nU p s ties tC hord d t e cls hdr hg
    obtain ⟨funs', nf, nb, a, hfuns, hG⟩ := gathers_layers_some L p4 nU p s a₀ ties tC tD hord hs
    obtain rfl : a₀.tl = tl := Option.some.inj ((lay_tl s a₀ hs).symm.trans ht)
    rw [lay_funs s a₀ hs] at hf
    cases ho : a₀.own with
    | none =>
      rw [ho] at hf
      exact absurd hf (by simp)
    | some o =>
      rw [ho] at hf
      obtain rfl : o.funs = funs := Option.some.inj hf
      rw [hfuns o ho] at hG
      exact ⟨nf, nb, a, hG⟩
  · exact ⟨0, 0, fun _ _ _ _ => 0,
      ⟨fun d t e cls hdr hg => absurd ⟨d, t, e, cls, hdr, hg⟩ hyes⟩⟩

/-- **The count at a feed-forward segment's batching.** batch: a decision each of whose yeses at s is
a yes of the batching block at the frame's function of claims, with the same return. -/
theorem fall_few_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s : S) (tU d : Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = orderOf .layers)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (hU : ∀ tl, s.tl? = some tl → unitsLaid nU tl tU = true)
    (hd : ∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
      F.planClaimsF + topOf tl funs ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch (zeroUnitAt nU) s [chiAt x] = true) ≤
      nU.getD 2 0 * d := by
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch (zeroUnitAt nU) s [chiAt x] = true
  · obtain ⟨x, hx⟩ := hne
    unfold askBehind at hx
    simp only [List.map_cons, List.map_nil] at hx
    cases hbt : batch s [⟨[], chiAt x⟩] with
    | error e =>
      rw [hbt] at hx
      exact absurd hx (by simp)
    | ok t' =>
      obtain ⟨t, e, cls, y, G, hdr, hg, -, -, -⟩ := batch_ok p _ s t' (chiAt x) (hb _ _ hbt)
      obtain ⟨a₀, hs⟩ := layers_here L p4 nU p s ties tC hord (chiAt x) t e cls hdr hg
      obtain ⟨gC, gD, o, lf, -, -, ho, -, -⟩ :=
        layers_walk L p4 nU p s a₀ ties tC tD hord hs (chiAt x) t e cls hdr hg
      have ht : s.tl? = some a₀.tl := lay_tl s a₀ hs
      have hF : s.fork? = some a₀.F := lay_fork s a₀ hs
      have hf : s.funs? = some o.funs := by
        rw [lay_funs s a₀ hs, ho]
        rfl
      obtain ⟨nf, nb, a, hG⟩ := gathers_layers_any L p4 nU p s a₀.tl o.funs ties tC tD hord ht hf
      exact fall_few p (claimsInBy L.each L.hear L.order) batch nU s a₀.tl a₀.F o.funs tU nf nb d a hb
        ((tlFork_iff s a₀.tl a₀.F).2 ⟨ht, hF⟩) (hU _ ht) hG (hd _ _ _ ht hF hf)
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.fall_few_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.layers_here
#print axioms VerifiableInference.Desc.First.K8.Honest.gathers_layers_any
