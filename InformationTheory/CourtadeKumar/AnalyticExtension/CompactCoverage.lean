import InformationTheory.CourtadeKumar.AnalyticExtension.CompactIntegerCheckerSound
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactData

/-! Compose the checked subtrees by real box coverage. No combined arithmetic replay. -/
namespace CourtadeKumar.LRCompactReducedCertificate
lemma logTwo_contains : logTwo.Contains (Real.log 2) := by
  simpa only [logTwo, Rat.cast_ofNat] using
    LRMidpointReducedCertificate.RoundedLog.sound logTwo_checked

def BoxSound (box : CertificateBox) : Prop :=
  ∀ p, box.Contains p → Physical p → 0 ≤ lrLowVReserve p.s p.k p.chi

theorem BoxSound.join {box : CertificateBox} (axis : CertificateAxis) (cut : ℚ)
    (hl : BoxSound (box.lower axis cut)) (hu : BoxSound (box.upper axis cut)) : BoxSound box := by
  intro p hp hphys
  rcases box.contains_lower_or_upper hp axis cut with h | h
  · exact hl p h hphys
  · exact hu p h hphys

private theorem batch000_sound : BoxSound Batch000.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch000.checked

private theorem batch001_sound : BoxSound Batch001.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch001.checked

private theorem batch002_sound : BoxSound Batch002.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch002.checked

private theorem batch003_sound : BoxSound Batch003.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch003.checked

private theorem batch004_sound : BoxSound Batch004.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch004.checked

private theorem batch005_sound : BoxSound Batch005.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch005.checked

private theorem batch006_sound : BoxSound Batch006.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch006.checked

private theorem batch007_sound : BoxSound Batch007.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch007.checked

private theorem batch008_sound : BoxSound Batch008.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch008.checked

private theorem batch009_sound : BoxSound Batch009.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch009.checked

private theorem batch010_sound : BoxSound Batch010.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch010.checked

private theorem batch011_sound : BoxSound Batch011.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch011.checked

private theorem batch012_sound : BoxSound Batch012.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch012.checked

private theorem batch013_sound : BoxSound Batch013.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch013.checked

private theorem batch014_sound : BoxSound Batch014.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch014.checked

private theorem batch015_sound : BoxSound Batch015.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch015.checked

private theorem batch016_sound : BoxSound Batch016.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch016.checked

private theorem batch017_sound : BoxSound Batch017.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch017.checked

private theorem batch018_sound : BoxSound Batch018.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch018.checked

private theorem batch019_sound : BoxSound Batch019.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch019.checked

private theorem batch020_sound : BoxSound Batch020.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch020.checked

private theorem batch021_sound : BoxSound Batch021.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch021.checked

private theorem batch022_sound : BoxSound Batch022.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch022.checked

private theorem batch023_sound : BoxSound Batch023.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch023.checked

private theorem batch024_sound : BoxSound Batch024.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch024.checked

private theorem batch025_sound : BoxSound Batch025.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch025.checked

private theorem batch026_sound : BoxSound Batch026.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch026.checked

private theorem batch027_sound : BoxSound Batch027.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch027.checked

private theorem batch028_sound : BoxSound Batch028.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch028.checked

private theorem batch029_sound : BoxSound Batch029.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch029.checked

private theorem batch030_sound : BoxSound Batch030.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch030.checked

private theorem batch031_sound : BoxSound Batch031.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch031.checked

private theorem batch032_sound : BoxSound Batch032.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch032.checked

private theorem batch033_sound : BoxSound Batch033.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch033.checked

private theorem batch034_sound : BoxSound Batch034.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch034.checked

private theorem batch035_sound : BoxSound Batch035.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch035.checked

private theorem batch036_sound : BoxSound Batch036.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch036.checked

private theorem batch037_sound : BoxSound Batch037.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch037.checked

private theorem batch038_sound : BoxSound Batch038.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch038.checked

private theorem batch039_sound : BoxSound Batch039.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch039.checked

private theorem batch040_sound : BoxSound Batch040.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch040.checked

private theorem batch041_sound : BoxSound Batch041.box :=
  LRCompactIntegerCertificate.checkTree_sound logTwo_contains Batch041.checked

theorem root_sound : BoxSound root := by
  exact (BoxSound.join .k (2 / 3)
  (BoxSound.join .s (9 / 20)
  batch000_sound
  (BoxSound.join .k (1 / 2)
  (BoxSound.join .s (27 / 40)
  batch001_sound
  (BoxSound.join .k (5 / 12)
  batch002_sound
  batch003_sound))
  (BoxSound.join .s (27 / 40)
  batch004_sound
  (BoxSound.join .k (7 / 12)
  batch005_sound
  batch006_sound))))
  (BoxSound.join .k (5 / 6)
  (BoxSound.join .s (9 / 20)
  batch007_sound
  (BoxSound.join .s (27 / 40)
  batch008_sound
  (BoxSound.join .k (3 / 4)
  (BoxSound.join .s (63 / 80)
  batch009_sound
  (BoxSound.join .chi (19 / 20)
  batch010_sound
  batch011_sound))
  (BoxSound.join .s (63 / 80)
  batch012_sound
  (BoxSound.join .chi (19 / 20)
  batch013_sound
  batch014_sound)))))
  (BoxSound.join .s (9 / 20)
  batch015_sound
  (BoxSound.join .k (11 / 12)
  (BoxSound.join .s (27 / 40)
  batch016_sound
  (BoxSound.join .chi (19 / 20)
  batch017_sound
  (BoxSound.join .s (63 / 80)
  batch018_sound
  (BoxSound.join .k (7 / 8)
  batch019_sound
  (BoxSound.join .chi (39 / 40)
  batch020_sound
  batch021_sound)))))
  (BoxSound.join .s (27 / 40)
  batch022_sound
  (BoxSound.join .chi (19 / 20)
  batch023_sound
  (BoxSound.join .k (23 / 24)
  (BoxSound.join .chi (39 / 40)
  batch024_sound
  (BoxSound.join .s (63 / 80)
  batch025_sound
  (BoxSound.join .k (15 / 16)
  batch026_sound
  batch027_sound)))
  (BoxSound.join .s (63 / 80)
  (BoxSound.join .chi (39 / 40)
  batch028_sound
  batch029_sound)
  (BoxSound.join .chi (39 / 40)
  batch030_sound
  (BoxSound.join .k (47 / 48)
  (BoxSound.join .chi (79 / 80)
  batch031_sound
  batch032_sound)
  (BoxSound.join .s (27 / 32)
  batch033_sound
  (BoxSound.join .chi (79 / 80)
  batch034_sound
  (BoxSound.join .k (95 / 96)
  batch035_sound
  (BoxSound.join .chi (159 / 160)
  batch036_sound
  (BoxSound.join .k (191 / 192)
  batch037_sound
  (BoxSound.join .s (279 / 320)
  batch038_sound
  (BoxSound.join .chi (319 / 320)
  batch039_sound
  (BoxSound.join .k (383 / 384)
  batch040_sound
  batch041_sound))))))))))))))))))

end CourtadeKumar.LRCompactReducedCertificate
