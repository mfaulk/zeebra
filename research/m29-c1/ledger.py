import json, sys
# Zeebra serial work ledger from an m29_cost_model --discovery record.
r = json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])
w = r["work"]; s = r["statistics"]
f, b = w["forward"], w["backward"]
fp, bp = f["coefficient_products"], b["coefficient_products"]
zp = sum(x["zero_row_products"] for x in w["batches"])
zr = sum(x["zero_rows"] for x in w["batches"])
zns = sum(x["zero_row_ns"] for x in w["batches"]); rns = sum(x["row_ns"] for x in w["batches"])
inh, disc = w["inherited_products"], w["discovered_products"]
print(r["target"], "status", r["status"], "basis", r["basis_sha256"][:12], "f4 ms", r["f4_call_ns"] / 1e6)
print(f"  pairs reduced {s['pairs_reduced']}, elements added {s['elements_added']}, zero rows {s['zero_rows']} (observed {zr})")
print(f"  forward products {fp/1e6:.1f} M (apps {f['pivot_applications']/1e6:.2f} M), backward {bp/1e6:.1f} M, total {(fp+bp)/1e6:.1f} M")
print(f"  forward inherited {inh/1e6:.1f} M ({inh/max(1,inh+disc):.1%}), discovered {disc/1e6:.1f} M")
print(f"  products on rows that end zero: {zp/1e6:.1f} M = {zp/max(1,fp):.1%} of forward, {zp/max(1,fp+bp):.1%} of all products")
print(f"  serial row time on zero rows: {zns/1e6:.0f} ms of {rns/1e6:.0f} ms ({zns/max(1,rns):.1%})")
print("  forward reducer-target ops", f["reducer_target_operations"], "pair-target ops", f["pair_target_operations"])
for x in w["batches"]:
    print(f"    deg {x['degree']:2} pairs {x['pairs']:5} rows {x['rows']:6} red {x['reducer_rows']:6} cols {x['columns']:6} rank {x['rank']:6} zero {x['zero_rows']:5} fwd {x['forward_products']/1e6:7.1f}M zero-row {x['zero_row_products']/1e6:7.1f}M bwd {x['backward_products']/1e6:7.1f}M")
