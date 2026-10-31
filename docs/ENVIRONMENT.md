# Environment and disk budget

The user requests work on the partition containing Ubuntu and monitoring of its
remaining space throughout development. The initialization workspace and `/`
are on the same ext4 device, `/dev/nvme2n1p4`. The initial available space was
about **26.8 GiB** (the system display rounds this to 27G).

The new Lean 4.36.0-rc2 toolchain is installed in the enclosing workspace's
`work/elan/`; it is separate from previously installed versions. New temporary
and cache directories are also in the enclosing `work/` directory. The existing
Lean installations and unrelated files are not removed.

Run `python3 scripts/check_disk.py` before and after downloads, builds and large
imports. It verifies that the repository is on the same device as the Ubuntu
root and prints available GiB. It warns below **10 GiB** and fails below
**5 GiB**. These are working thresholds chosen for this project and may be
tightened if the next operation needs a larger reserve.

Use selective Mathlib imports and cache downloads. With
`MATHLIB_NO_CACHE_ON_UPDATE=1`, dependency resolution does not automatically
download the entire Mathlib cache. Do not create duplicate checkouts or full
cache copies without checking their space cost. Remove only identified
regenerable project downloads when needed, preserving source and audit records.

Monitoring here is an explicit check during active work, not an installed
background service or scheduled automation. Report warnings to the user and
pause heavy operations if the reserve is insufficient.
