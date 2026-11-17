#!/usr/bin/env python3
"""GPL-workspace-only #716 controls, applied after the randomization overlay.

`research_handover=false` takes the pinned engine's own no-handover path (the one cofactor
tracking selects), so the signature run computes to the end; plain-F4 pair updates are tallied
passively by criterion. Nothing else in the solver changes.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent


def replace(source, old, new):
    if source.count(old) != 1:
        raise ValueError('signature anchor changed: ' + old[:80])
    return source.replace(old, new, 1)


def entry_gate(source):
    source = replace(source, '        let handover = engine.signature().then_some(on(!C::TRACKS));\n',
                     '        let handover = engine.signature().then_some(on(!C::TRACKS && crate::research_sig::handover_enabled()));\n')
    return replace(source, '                let handover = (!C::TRACKS).then_some(HANDOVER);\n',
                   '                let handover = (!C::TRACKS && crate::research_sig::handover_enabled()).then_some(HANDOVER);\n')


def pair_tally(source):
    return replace(source, '    new.kept.sort_unstable_by_key(|&(place, _, _)| place);\n',
                   '    crate::research_sig::plain_update(new.dropped.len(), basis.min().len() - new.elements.len(),\n'
                   '        new.sorted.len() - new.kept.len(), new.kept.len());\n'
                   '    new.kept.sort_unstable_by_key(|&(place, _, _)| place);\n')


def driver_main(text):
    text = replace(text, '    let signatures = research_bool(input, "research_signatures", true)?;\n',
                   '    let signatures = research_bool(input, "research_signatures", true)?;\n'
                   '    let handover = research_bool(input, "research_handover", true)?;\n')
    text = replace(text, '    let ((outcome, work), audit, events) = grobx::research_random::capture(policy, ||\n'
                         '        grobx::research_work::capture(enabled, || grobx::groebner(&text, &params)));',
                   '    let (((outcome, work), audit, events), signature) = grobx::research_sig::capture(handover, ||\n'
                   '        grobx::research_random::capture(policy, ||\n'
                   '        grobx::research_work::capture(enabled, || grobx::groebner(&text, &params))));')
    return replace(text, '    output["research_audit"] = json!(audit);\n',
                   '    output["research_audit"] = json!(audit);\n    output["research_signature"] = signature;\n')


def apply(source, driver):
    lib = source / 'src/lib.rs'
    lib.write_text(lib.read_text() + '\npub mod research_sig;\n')
    (source / 'src/research_sig.rs').write_text((HERE / 'policy.rs').read_text())
    entry = source / 'src/entry.rs'
    entry.write_text(entry_gate(entry.read_text()))
    pairs = source / 'src/pairs.rs'
    pairs.write_text(pair_tally(pairs.read_text()))
    main = driver / 'src/main.rs'
    main.write_text(driver_main(main.read_text()) + (HERE / 'driver-tests.rs').read_text())
