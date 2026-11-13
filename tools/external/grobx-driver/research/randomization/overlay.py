#!/usr/bin/env python3
"""GPL-workspace-only independent ablation gates; applied after the pinned passive observer."""
from pathlib import Path

HERE = Path(__file__).resolve().parent


def replace(source, old, new):
    if source.count(old) != 1:
        raise ValueError('randomization anchor changed: ' + old[:80])
    return source.replace(old, new, 1)


def matrix_policy(source):
    source = replace(source, '    p >= COMBINES_FROM\n',
                     '    crate::research_random::plain_enabled() && p >= COMBINES_FROM\n')
    return replace(source, '    F::LANES == 1 && zero_combinations(p).is_some()\n',
                   '    crate::research_random::signature_enabled() && F::LANES == 1 && zero_combinations(p).is_some()\n')


def apply(source, driver):
    lib = source / 'src/lib.rs'
    lib.write_text(lib.read_text() + '\npub mod research_random;\n')
    (source / 'src/research_random.rs').write_text((HERE / 'policy.rs').read_text())
    matrix = source / 'src/matrix.rs'
    text = matrix_policy(matrix.read_text())
    text = replace(text, '                if stopped {\n                    start = first;',
        '                crate::research_random::block(block.len(), pivots, done, stopped);\n                if stopped {\n                    start = first;')
    text = replace(text, '            if !passed {\n                tested.failed = true;',
        '            crate::research_random::group(group_len, s, passed);\n            if !passed {\n                tested.failed = true;')
    text = replace(text, '    if full {\n        budget.mark(Stage::Reduce);\n        red.back_substitute(cof, budget)?;\n        budget.mark(Stage::Backsub);\n    }\n    red.give_back(bufs);\n    Ok(Reduction {',
        '    red.research_validate::<M>(budget)?;\n    if full {\n        budget.mark(Stage::Reduce);\n        red.back_substitute(cof, budget)?;\n        budget.mark(Stage::Backsub);\n    }\n    red.give_back(bufs);\n    Ok(Reduction {')
    method = '''    fn research_validate<M: Format>(&mut self, budget: &mut Budget) -> Result<(), Stop> {
        if !crate::research_random::validate_enabled() { return Ok(()); }
        let started = std::time::Instant::now();
        let before = budget.counts();
        crate::research_work::phase(3);
        let mut valid = true;
        for index in 0..self.matrix.rows.len() {
            budget.tick()?;
            let r = RowId::at(index);
            let row = self.reduce::<M, NoCofactors>(r, self.matrix.lead(r), &mut NoCofactors, budget)?;
            valid &= row.cols.is_empty();
        }
        let after = budget.counts();
        crate::research_random::checked(self.matrix.rows.len(), self.matrix.columns(), valid,
            started.elapsed().as_nanos() as u64, after.0 - before.0, after.1 - before.1);
        crate::research_work::phase(0);
        Ok(())
    }

'''
    text = replace(text, '    fn research_snapshot(&self, extra: Option<&Reduced<F>>) {',
                   method + '    fn research_snapshot(&self, extra: Option<&Reduced<F>>) {')
    matrix.write_text(text)
    work = source / 'src/research_work.rs'
    text = work.read_text().replace('[Counts; 3]', '[Counts; 4]').replace('[Counts::default(); 3]', '[Counts::default(); 4]')
    text = text.replace('"combination": m.phases[2].json(),',
                        '"combination": m.phases[2].json(), "validation": m.phases[3].json(),')
    work.write_text(text)
    main = driver / 'src/main.rs'
    text = main.read_text()
    text = replace(text, '    let mut params = grobx::Params::new(', '''    let seed = match input.get("research_seed") {
        None => 0,
        Some(value) => value.as_u64().ok_or("invalid research_seed")?,
    };
    let policy = match input.get("research_policy") {
        None => "native",
        Some(value) => value.as_str().ok_or("invalid research_policy")?,
    };
    let signatures = research_bool(input, "research_signatures", true)?;
    let validate = research_bool(input, "research_validate", false)?;
    if validate && (signatures || mode != "raw") { return Err("residual validation requires plain-only raw mode".into()); }
    let mut params = grobx::Params::new(''')
    text = replace(text, '        0,\n    );\n    params.report = true;',
        '        seed,\n    );\n    params.signatures = signatures;\n    params.report = true;')
    old = '    let (outcome, work) = grobx::research_work::capture(enabled, || grobx::groebner(&text, &params));'
    new = '''    let policy = grobx::research_random::Policy::named(policy, validate)?.observed(enabled);
    let ((outcome, work), audit, events) = grobx::research_random::capture(policy, ||
        grobx::research_work::capture(enabled, || grobx::groebner(&text, &params)));
    if audit.iter().any(|row| row["valid"] != true) { return Err("residual-span validation failed".into()); }'''
    text = replace(text, old, new)
    text = replace(text, '    output["work"] = work.map_or(Value::Null, |s| s.json());',
        '    output["work"] = work.map_or(Value::Null, |s| s.json());\n    output["research_audit"] = json!(audit);\n    output["research_events"] = json!(events);\n    output["research_policy"] = json!({"plain":policy.plain,"signature_tests":policy.signature,"validate":validate,"signatures":signatures,"seed":seed});')
    text += '\nfn research_bool(input: &Value, key: &str, default: bool) -> Result<bool, String> {\n    match input.get(key) { None => Ok(default), Some(value) => value.as_bool().ok_or_else(|| format!("invalid {key}")) }\n}\n'
    text += (HERE / 'driver-tests.rs').read_text()
    main.write_text(text)
