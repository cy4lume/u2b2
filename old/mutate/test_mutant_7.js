function __wrapper__(origFn, mutFn, origArgs, mutArgs) {
    const oVal = origFn(...origArgs);
    const mVal = mutFn(...mutArgs);
    console.assert(typeof oVal === typeof mVal) 
    return mVal;
}

function a(a, b) {
    console.log(a, b);
    return a | b;
}
function mutated_a(a, b) {
    console.log(a, b);
    return a | b;
}
__wrapper__(a, mutated_a, [
    1,
    4
], [
    1,
    {
        vvz: 3,
        uvw: 3,
        ywx: 6
    }
]);