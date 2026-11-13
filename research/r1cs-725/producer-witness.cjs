const fs = require('node:fs');
const path = require('node:path');

const directory = path.resolve(process.argv[2]);
const calculate = require(path.join(directory, 'witness_calculator.js'));
const input = JSON.parse(fs.readFileSync(process.argv[3], 'utf8'));
calculate(fs.readFileSync(path.join(directory, 'multiplier.wasm'))).then(async calculator => {
    const witness = (await calculator.calculateWitness(input, 0)).map(value => value.toString());
    console.log(JSON.stringify({input, witness}, null, 2));
});
