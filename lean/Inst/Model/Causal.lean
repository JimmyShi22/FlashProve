-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Causal.lean: the integer program is causal: the residual stream at position pos, and so
the logits at pos, depend only on the tokens 0 .. pos.
    `FF.x''_congr`, `Att.x'_congr`  block by block
    `XK_causal`, `lgK_causal`       the stream and the logits
    `gap_causal_R`                  so what comes after the last checked token (the padding)
                                    changes no covered gap
Notation (Inst/Model/Program.lean; the last two: Inst/Model/ProgramR.lean):
  `tb`: a `Tables`, "The five table functions that the program reads."
  `w`: a `LayerW`, "The weight matrices of one layer."
  `L`: a natural number, the number of the layer (`XK`: "with layer L at its scales and tables").
  `κ`: a map `ℕ → LayerScale`; a `LayerScale`: "The scales of one layer."
  `nf`: a `NormPar`, "exponent of the reciprocal; shift; constant" of a normalisation: of the final
    one (`nrmK`).
  `tbs`: a map `ℕ → Tables`, the tables of each layer.
  the stream `x`, in the lemmas on one layer (up to `Att.x'_congr`): a map `ℕ → Vec`, from a
    position to its vector (`Vec`: `ℕ → ℤ`); "The residual stream" (`X`).
  `XK P κ tbs i p l pos`: a `Vec` (`l`: the λ of `X`, "X_λ, λ = 0, ..., 2·layers"); "The residual
    stream, with layer L at its scales and tables."
  `lgK P κ nf tbs i p pos`: a map `ℕ → ℤ`; the logits, `lg` ("(PH2) lg_i[ι] = Σ_j nrm_i[j] H[j][ι]")
    "with the scales and tables of each layer".
  `maxTo f n`: an integer, "max_{j ≤ n} f(j)".
  `i`: in the lemmas on one layer a natural number, a position (so too in the quoted (PH2)); from
    `XK_causal` on a `Weights`, "An index: the weight tensors, as integers, ..".
  `x`, in `gap_causal_R`: an `Instance P`, "a request: T tokens, the announced token y, and the two
    numbers r, e"; "the covered positions: r ≤ t < e".
  `x.w t`: a natural number, "the checked token of position t": `x.tok (t + 1)`.
  `gapOf V l w`: an integer, "the logit gap of the token w: max_(v < V) (l[v] − l[w] + [v < w])".
Limits: `RunsK`, "no range condition fails", is asked at all T positions and does read the
padding: a padding can take an instance out of the relation.
-/
import Inst.Model.ProgramR

set_option autoImplicit false

namespace Inst.Model

theorem maxTo_congr' {f g : Vec} : ∀ n : ℕ, (∀ j ≤ n, f j = g j) → maxTo f n = maxTo g n
  | 0, h => h 0 le_rfl
  | n + 1, h => by
      show max (maxTo f n) (f (n + 1)) = max (maxTo g n) (g (n + 1))
      rw [maxTo_congr' n fun j hj => h j (Nat.le_succ_of_le hj), h (n + 1) le_rfl]

section Layer
variable (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) {x x' : ℕ → Vec}

/-- a feed-forward block reads the stream at its own position -/
theorem FF.x''_congr {i : ℕ} (h : x i = x' i) : FF.x'' P tb w L x i = FF.x'' P tb w L x' i := by
  have hm : FF.m P x i = FF.m P x' i := by unfold FF.m; rw [h]
  have hlw : FF.lw P w x i = FF.lw P w x' i := by funext e; simp only [FF.lw, hm]
  have hl3 : FF.l3 P w x i = FF.l3 P w x' i := by funext e; simp only [FF.l3, hlw]
  have hly : FF.ly P w x i = FF.ly P w x' i := by funext e; simp only [FF.ly, hlw, hl3]
  have hlr : FF.lr P w x i = FF.lr P w x' i := by funext e; simp only [FF.lr, hly, hl3]
  have hes : FF.es P w x i = FF.es P w x' i := by simp only [FF.es, hlr]
  have hmr : FF.mr P w x i = FF.mr P w x' i := by simp only [FF.mr, hlr, hes]
  have hsc : FF.sc P tb w x i = FF.sc P tb w x' i := by simp only [FF.sc, hmr]
  have hxr : FF.xr P tb w x i = FF.xr P tb w x' i := by funext j; simp only [FF.xr, hsc, hm]
  have hz : ∀ j, FF.z P tb w L x i j = FF.z P tb w L x' i j := fun j => by simp only [FF.z, hxr, hm]
  have hwg : ∀ j, FF.wg P w L x i j = FF.wg P w L x' i j :=
    fun j => by funext t; simp only [FF.wg, hes]
  have hwu : ∀ j, FF.wu P w L x i j = FF.wu P w L x' i j :=
    fun j => by funext t; simp only [FF.wu, hes]
  have hhh : ∀ j, FF.hh P tb w L x i j = FF.hh P tb w L x' i j :=
    fun j => by simp only [FF.hh, hz, hwg, hwu]
  funext c
  simp only [FF.x'', FF.Ad, hhh, hes, h]

theorem Att.q_congr {i : ℕ} (h : x i = x' i) (c : ℕ) :
    Att.q P tb w L x i c = Att.q P tb w L x' i c := by
  simp only [Att.q, Att.qkw, Att.Y', Att.AY, Att.Aq, Att.Ak, Att.a, h]
theorem Att.kx_congr {i : ℕ} (h : x i = x' i) (c : ℕ) :
    Att.kx P tb w L x i c = Att.kx P tb w L x' i c := by
  simp only [Att.kx, Att.qkw, Att.Y', Att.AY, Att.Aq, Att.Ak, Att.a, h]
theorem Att.v_congr {i : ℕ} (h : x i = x' i) (c : ℕ) : Att.v P w x i c = Att.v P w x' i c := by
  simp only [Att.v, Att.vw, Att.Av, Att.a, h]

theorem Att.sc_congr {i j : ℕ} (hi : x i = x' i) (hj : x j = x' j) (hd : ℕ) :
    Att.sc P tb w L x hd i j = Att.sc P tb w L x' hd i j := by
  unfold Att.sc
  exact Finset.sum_congr rfl fun n _ => by rw [Att.q_congr P tb w L hi, Att.kx_congr P tb w L hj]

/-- an attention block reads the stream at the positions up to its own -/
theorem Att.x'_congr {i : ℕ} (h : ∀ j ≤ i, x j = x' j) :
    Att.x' P tb w L x i = Att.x' P tb w L x' i := by
  have hsc : ∀ hd, ∀ j ≤ i, Att.sc P tb w L x hd i j = Att.sc P tb w L x' hd i j := fun hd j hj =>
    Att.sc_congr P tb w L (h i le_rfl) (h j hj) hd
  have hmx : ∀ hd, Att.mx P tb w L x hd i = Att.mx P tb w L x' hd i := fun hd =>
    maxTo_congr' i (hsc hd)
  have hwt : ∀ hd,
      ∀ j ≤ i, Att.wt P tb w L x hd i j = Att.wt P tb w L x' hd i j := fun hd j hj => by
    simp only [Att.wt, Att.u, hmx hd, hsc hd j hj]
  have hden : ∀ hd, Att.den P tb w L x hd i = Att.den P tb w L x' hd i := fun hd =>
    Finset.sum_congr rfl fun j hj => hwt hd j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have hac : ∀ hd n, Att.ac P tb w L x hd i n = Att.ac P tb w L x' hd i n := fun hd n =>
    Finset.sum_congr rfl fun j hj => by
      have hj' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [hwt hd j hj', Att.v_congr P w (h j hj')]
  have ho : Att.o P tb w L x i = Att.o P tb w L x' i := by
    funext c
    simp only [Att.o, hac, hden]
  funext c
  simp only [Att.x', ho, h i le_rfl]

end Layer

section Program
variable (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (i : Weights)

/-- The stream is causal: two prompts that agree on the tokens 0 .. n give the same stream at every
position ≤ n, in all layers. -/
theorem XK_causal {p p' : Fin P.T → Fin P.V} {n : ℕ}
    (h : ∀ t (ht : t < P.T), t ≤ n → p ⟨t, ht⟩ = p' ⟨t, ht⟩) :
    ∀ l pos, pos ≤ n → XK P κ tbs i p l pos = XK P κ tbs i p' l pos
  | 0, pos, hp => by
      funext j
      show (if h : pos < P.T then i.Emb (p ⟨pos, h⟩) j else 0) =
        if h : pos < P.T then i.Emb (p' ⟨pos, h⟩) j else 0
      split
      · rename_i hT
        rw [h pos hT hp]
      · rfl
  | l + 1, pos, hp => by
      show (if l % 2 = 0 then Att.x' _ _ _ _ (XK P κ tbs i p l)
          else FF.x'' _ _ _ _ (XK P κ tbs i p l)) pos =
        (if l % 2 = 0 then Att.x' _ _ _ _ (XK P κ tbs i p' l)
          else FF.x'' _ _ _ _ (XK P κ tbs i p' l)) pos
      split
      · exact Att.x'_congr _ _ _ _ fun j hj => XK_causal h l j (le_trans hj hp)
      · exact FF.x''_congr _ _ _ _ (XK_causal h l pos hp)

theorem lgK_causal {p p' : Fin P.T → Fin P.V} {n : ℕ}
    (h : ∀ t (ht : t < P.T), t ≤ n → p ⟨t, ht⟩ = p' ⟨t, ht⟩) {pos : ℕ} (hp : pos ≤ n) :
    lgK P κ nf tbs i p pos = lgK P κ nf tbs i p' pos := by
  funext v
  simp only [lgK, nrmK, XK_causal P κ tbs i h _ pos hp]

/-- The padding changes no covered gap: two instances whose `tok` t agree for all t ≤ n (`tok` T is
y, the announced token) have the same gap (`gapOf`, at the logits of position t and its checked
token `x.w t`) at every position t with t + 1 ≤ n. (Gap, covered: Notation, in the comment at the
top.) -/
theorem gap_causal_R {x x' : Instance P} {n : ℕ} (h : ∀ t ≤ n, x.tok t = x'.tok t)
    {t : ℕ} (ht : t + 1 ≤ n) :
    gapOf P.V (lgK P κ nf tbs i x.prompt t) (x.w t) =
      gapOf P.V (lgK P κ nf tbs i x'.prompt t) (x'.w t) := by
  have hp : ∀ s (hs : s < P.T), s ≤ n → x.prompt ⟨s, hs⟩ = x'.prompt ⟨s, hs⟩ := fun s hs hn => by
    have := h s hn
    unfold Instance.tok at this
    rw [dif_pos hs, dif_pos hs] at this
    exact Fin.ext this
  rw [lgK_causal P κ nf tbs i hp (by omega : t ≤ n)]
  show gapOf P.V _ (x.tok (t + 1)) = gapOf P.V _ (x'.tok (t + 1))
  rw [h (t + 1) ht]

end Program

end Inst.Model
