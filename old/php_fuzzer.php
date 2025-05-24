#!/usr/bin/env php
<?php
/**
 * To Install: `composer require nikic/php-parser:^2`
 * 
 *  Random PHP code generator — PHP‑Parser 2.x / PHP 5.6
 *
 * Flags
 *   --easy             Shorter code
 *   --no-builtin       Disable builtin calls entirely
 *   --wrap-builtin     Emit wrapper($fn, [$args]) around builtin call
 *   --typed-builtin    Use only functions present in $TYPE_HINT *and* generate
 *                      arguments that match their simple type signature.
 */

require __DIR__ . '/vendor/autoload.php';

use PhpParser\BuilderFactory;
use PhpParser\PrettyPrinter\Standard as Printer;
use PhpParser\Node;
use PhpParser\Node\Stmt;
use PhpParser\Node\Expr;

// ───────────────────────────── helpers
function ri($a, $b) { return function_exists('random_int') ? random_int($a, $b) : mt_rand($a, $b); }
function rand_str($n = 5) { $s = ''; for ($i = 0; $i < $n; $i++) $s .= chr(ri(97, 122)); return $s; }
function opts() { return getopt('n::', ['print', 'easy', 'seed::', 'out::', 'no-builtin', 'wrap-builtin', 'typed-builtin']); }
function expr_stmt(Node $n) { return $n; } // v2.x: raw node allowed in stmt list

// ───────────────────────────── typed signature table (positional)
$TYPE_HINT = [
    // string f(int?, int?) style
    'substr'      => ['string', 'int', 'int'],
    'strpos'      => ['string', 'string', 'int'],  // haystack, needle, offset
    'strlen'      => ['string'],
    'strtoupper'  => ['string'],
    'strtolower'  => ['string'],
    'strrev'      => ['string'],
    // numeric
    'abs'   => ['int'],
    'sqrt'  => ['int'],
    'intval'=> ['int'],
    'pow'   => ['int', 'int'],
    'max'   => ['int', 'int'],
    'min'   => ['int', 'int'],
    'rand'  => ['int', 'int'],
];

// ───────────────────────────── builtin catalogue (with min/max arg counts)
function collect_builtins() {
    $tbl = [];
    foreach (get_defined_functions()['internal'] as $fn) {
        if (strpos($fn, 'php_') === 0 || in_array($fn, ['exit', 'die'])) continue;
        $r = new ReflectionFunction($fn);
        $tbl[$fn] = [$r->getNumberOfRequiredParameters(), $r->getNumberOfParameters() ?: $r->getNumberOfRequiredParameters()];
    }
    return $tbl;
}
$BUILT_IN_ALL = collect_builtins();

// choose random literal by type
function lit_by_type($type) {
    return ($type === 'string')
        ? new Node\Scalar\String_(rand_str())
        : new Node\Scalar\LNumber(ri(-5000, 5000));
}

// ───────────────────────────── expression generator factory
function make_expr_gen(array &$vars, array &$builtPool, $use, $wrap, $typed, array &$typeHint) {
    $gen = null;
    $gen = function ($d = 0) use (&$gen, &$vars, &$builtPool, $use, $wrap, $typed, &$typeHint) {
        // builtin leaf
        if ($use && $d > 0 && ri(1, 100) <= 25) {
            $available = $typed ? array_intersect_key($builtPool, $typeHint) : $builtPool;
            if (!$available) return new Node\Scalar\LNumber(0); // fallback
            $fn   = array_rand($available);
            list($min, $max) = $available[$fn];
            $sig  = $typed && isset($typeHint[$fn]) ? $typeHint[$fn] : [];
            $argc = $typed && $sig ? count($sig) : ri($min, min($max, 4));

            $exprArgs = [];
            $arrItems = [];
            for ($i = 0; $i < $argc; $i++) {
                if ($typed && isset($sig[$i])) {
                    $expr = lit_by_type($sig[$i]);
                } else {
                    // default literal or variable
                    $expr = ri(0, 1)
                        ? new Node\Scalar\LNumber(ri(-50, 50))
                        : new Node\Scalar\String_(rand_str());
                }
                // occasionally make first arg a variable for variability
                if ($i == 0 && ri(0, 1) && !$typed) $expr = new Expr\Variable($vars[array_rand($vars)]);
                $exprArgs[] = $expr;             // direct call args
                $arrItems[] = new Expr\ArrayItem($expr); // wrapper array items
            }
            return $wrap ? new Expr\FuncCall(new Node\Name('wrapper'), [
                        new Node\Scalar\String_($fn),
                        new Expr\Array_($arrItems)
                    ]) : new Expr\FuncCall(new Node\Name($fn), $exprArgs);
        }
        // leaf literal or variable
        if ($d > 2 || ri(0, 1) === 0) {
            return ri(0, 1) ? new Expr\Variable($vars[array_rand($vars)])
                            : (ri(0, 1) ? new Node\Scalar\LNumber(ri(-5000, 5000))
                                         : new Node\Scalar\LNumber(ri(-5000,5000)));
        }
        // binary op
        $ops = ['Plus','Minus','Mul','Div','Mod','BitwiseXor','BitwiseOr','BitwiseAnd'];
        $cls = 'PhpParser\\Node\\Expr\\BinaryOp\\' . $ops[array_rand($ops)];
        return new $cls($gen($d + 1), $gen($d + 1));
    };
    return $gen;
}

// ───────────────────────────── program generator (no while loops)
function gen_program($easy, array &$opt, array &$typeHint) {
    global $BUILT_IN_ALL;
    $factory = new BuilderFactory();
    $stmts   = [];
    $vars    = [];

    for ($i = 0, $g = $easy ? ri(2, 4) : ri(3, 8); $i < $g; $i++) {
        $name    = chr(ri(97, 122)) . ri(0, 99);
        $vars[]  = $name;
        $stmts[] = expr_stmt(new Expr\Assign(new Expr\Variable($name), new Node\Scalar\LNumber(ri(-5000, 5000))));
    }

    $exprGen = make_expr_gen($vars, $BUILT_IN_ALL, $opt['use'], $opt['wrap'], $opt['typed'], $typeHint);
    $makeAssign = function () use (&$vars, &$exprGen) {
        $t = $vars[array_rand($vars)];
        return expr_stmt(new Expr\Assign(new Expr\Variable($t), $exprGen()));
    };

    for ($i = 0, $cnt = $easy ? ri(4, 6) : ri(6, 15); $i < $cnt; $i++) {
        ($i & 1) ? $stmts[] = $makeAssign() : $stmts[] = $exprGen();

        if (ri(0, 1) === 0) {
            $stmts[] = new Stmt\If_($exprGen(), ['stmts' => [$makeAssign()]]);
        }
        if (ri(0, 1) === 0) {
            $lv   = 'i' . ri(0, 99);
            $init = [new Expr\Assign(new Expr\Variable($lv), new Node\Scalar\LNumber(0))];
            $cond = [new Expr\BinaryOp\Smaller(new Expr\Variable($lv), new Node\Scalar\LNumber(ri(2, 10)))] ;
            $step = [new Expr\PostInc(new Expr\Variable($lv))];
            $stmts[] = new Stmt\For_(['init' => $init, 'cond' => $cond, 'loop' => $step, 'stmts' => [$makeAssign()]]);
        }
    }

    $stmts[] = new Stmt\Return_(new Expr\Variable($vars[array_rand($vars)]));

    $mainFunc = $factory->function('main')->addStmts($stmts)->getNode();
    return (new Printer())->prettyPrintFile([$mainFunc, new Expr\FuncCall(new Node\Name('main'))]);
}

// ───────────────────────────── entrypoint
function write_p($code, $dir, $idx) {
    if (!is_dir($dir) && !mkdir($dir, 0777, true)) die("mkdir failed");
    $p = rtrim($dir, '/\\') . "/prog_{$idx}.php";
    file_put_contents($p, $code);
    return $p;
}

function main(array &$typeHint) {
    $o = opts();
    $opt = [
        'easy'  => isset($o['easy']),
        'use'   => !isset($o['no-builtin']),
        'wrap'  => isset($o['wrap-builtin']),
        'typed' => isset($o['typed-builtin']),
    ];

    if (isset($o['seed']) && $o['seed'] !== false) {
        mt_srand((int)$o['seed']);
    }

    // single program to stdout
    if (!isset($o['n']) || isset($o['print'])) {
        echo gen_program($opt['easy'], $opt, $typeHint) . "
";
        return;
    }

    // bulk generation
    $n   = (int) $o['n'];
    $out = (isset($o['out']) && $o['out'] !== false) ? $o['out'] : __DIR__ . '/generated';
    echo "[*] Generating $n programs into $out ...
";
    for ($i = 1; $i <= $n; $i++) {
        $code = gen_program($opt['easy'], $opt, $typeHint);
        echo "[+] " . write_p($code, $out, $i) . "
";
    }
}

main($TYPE_HINT);
