import path from 'node:path';
import {pathToFileURL} from 'node:url';

const {readR1cs} = await import(pathToFileURL(path.resolve(process.argv[2], 'src/r1csfile.js')));
const result = [];
for (const filename of process.argv.slice(3)) {
    const model = await readR1cs(filename, {loadConstraints:true, loadMap:true, singleThread:true});
    result.push({
        file:filename, n8:model.n8, prime:model.prime.toString(), nWires:model.nVars,
        nPublicOutputs:model.nOutputs, nPublicInputs:model.nPubInputs, nPrivateInputs:model.nPrvInputs,
        nLabels:model.nLabels, nConstraints:model.nConstraints, map:Array.from(model.map, Number),
        constraints:Array.from(model.constraints, row => row.map(lc => Object.fromEntries(
            Object.entries(lc).map(([wire, coefficient]) => [wire, model.F.toObject(coefficient).toString()])
        )))
    });
    if (model.curve) await model.curve.terminate();
}
console.log(JSON.stringify(result, null, 2));
