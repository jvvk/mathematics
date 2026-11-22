#!/bin/zsh
# Deletes every generated data file, regenerates all of them from nothing and runs every filter and audit, in
# order. Stops at the first failure. About 5 minutes (residue_claude.py needs Singular).
set -e
cd "${0:A:h}"
rm -f m[4-7]_*.json residue_claude_*.json jets_claude_*.json
t() { local s=$SECONDS; echo "\$ python3 $*"; python3 "$@"; echo "  [$(( SECONDS - s )) s]"; }
# Configurations (first enumeration) and the first implementation's filters, degrees 4 to 6.
for m in 4 5 6 7; do t mconfigs.py $m; done
for m in 4 5 6; do t pipeline.py $m; done
t centre_distinct.py
t check_centre_distinct_algebra.py
t centre_sextic.py
t check_centre_sextic_algebra.py
# The independent re-implementation and the algebra checks.
t audit_sextic.py
t verify_sec5.py
# Second enumeration, running the whole chain of conditions; writes m7_survivors.json (530).
for m in 4 5 6 7; do t enum_indep.py $m; done
# Certificates for every group-law exclusion in degrees 5 and 6, checked by separate code.
t torsion_certificates.py 6
t grouplaw_certificates.py
t check_grouplaw_certificates.py
# Degree seven.
t centre_septic.py 7
t centre_septic.py 4 5 6 --source configs --tag fibre_reciprocity_calibration
t check_centre_septic.py
t check_septic_claude.py m7_fibre_reciprocity_certificates.json
t m7_targets.py split
t offcentre_residue.py
t check_offcentre_residue.py
t residue_claude.py m7_offcentre_targets.json --expect-unit m7_residue_certificates.json
t m7_targets.py open
t septic_jet_filter.py m7_open134.json m4_configs.json m5_configs.json m6_configs.json
t check_septic_jets.py
t jets_claude.py m7_open134.json
echo CHAIN DONE
