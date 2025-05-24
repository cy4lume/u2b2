#!/usr/bin/env php
<?php
/**
 * To Install: `composer require nikic/php-parser:^2`
 * 
 * Random PHP code generator (PHP‑Parser 2.x / PHP 5.6).
 *   • Pure v2 API — no shim classes.
 *   • `--no-builtin` flag disables random built‑in calls.
 *   • Loop and branch bodies now always contain **assignment statements** (not just bare expressions).
 */

require __DIR__ . '/vendor/autoload.php';

use PhpParser\BuilderFactory;
use PhpParser\PrettyPrinter\Standard as Printer;
use PhpParser\Node;
use PhpParser\Node\Stmt;
use PhpParser\Node\Expr;

//──────────────────────── Helpers
function ri($a, $b) { return function_exists('random_int') ? random_int($a, $b) : mt_rand($a, $b); }
function opts()      { return getopt('n::', ['print', 'easy', 'seed::', 'out::', 'no-builtin']); }
function expr_stmt(Node $e) { return $e; } // v2 accepts raw Node in stmt list

//──────────────────────── Built‑in catalogue
function builtins() {
    $tbl = [];
    foreach (get_defined_functions()['internal'] as $fn) {
        if (strpos($fn, 'php_') === 0 || in_array($fn, ['exit', 'die'])) continue;
        $r   = new ReflectionFunction($fn);
        $min = $r->getNumberOfRequiredParameters();
        $max = $r->getNumberOfParameters();
        if ($max === 0) continue;
        $tbl[$fn] = [$min, $max ?: $min];
    }
    return $tbl;
}
$BUILT_INS = builtins();

//──────────────────────── Expression builder
function make_expr_gen(array &$vars, array &$built, $useBuilt) {
    $gen = null;
    $gen = function ($d = 0) use (&$gen, &$vars, &$built, $useBuilt) {
        if ($useBuilt && $d > 0 && ri(1, 100) <= 25) {
            $fn   = array_rand($built); list($min, $max) = $built[$fn];
            $argc = ri($min, min($max, 4));
            $args = [];
            for ($i = 0; $i < $argc; $i++) {
                $args[] = new Node\Arg(
                    $d > 2 ? new Node\Scalar\LNumber(ri(-20, 20))
                            : ($i === 0 ? new Expr\Variable($vars[array_rand($vars)])
                                         : new Node\Scalar\LNumber(ri(-50, 50)))
                );
            }
            return new Expr\FuncCall(new Node\Name($fn), $args);
        }
        if ($d > 2 || ri(0, 1) === 0) {
            return ri(0, 1) ? new Expr\Variable($vars[array_rand($vars)])
                            : new Node\Scalar\LNumber(ri(-5000, 5000));
        }
        $ops = ['Plus','Minus','Mul','Div','Mod','BitwiseXor','BitwiseOr','BitwiseAnd'];
        $cls = 'PhpParser\\Node\\Expr\\BinaryOp\\' . $ops[array_rand($ops)];
        return new $cls($gen($d + 1), $gen($d + 1));
    };
    return $gen;
}

//──────────────────────── Program generator
function gen_program($easy, array &$built, $useBuilt) {
    $factory = new BuilderFactory();
    $stmts   = [];

    // global vars
    $vars = [];
    for ($i = 0, $g = $easy ? ri(2, 4) : ri(3, 8); $i < $g; $i++) {
        $name   = chr(ri(97, 122)) . ri(0, 99);
        $vars[] = $name;
        $stmts[] = expr_stmt(new Expr\Assign(new Expr\Variable($name), new Node\Scalar\LNumber(ri(-5000, 5000))));
    }

    $exprGen = make_expr_gen($vars, $built, $useBuilt);

    // body factory: always an assignment to a random var
    $makeAssign = function () use (&$vars, &$exprGen) {
        $t = $vars[array_rand($vars)];
        return expr_stmt(new Expr\Assign(new Expr\Variable($t), $exprGen()));
    };

    // random top‑level statements
    for ($i = 0, $cnt = $easy ? ri(4, 6) : ri(6, 15); $i < $cnt; $i++) {
        // top‑level: 40% bare expr, 60% assignment
        if (ri(1, 100) <= 40) {
            $stmts[] = expr_stmt($exprGen());
        } else {
            $stmts[] = $makeAssign();
        }

        // optional if
        if (ri(0, 1) === 0) {
            $cond = new Expr\BinaryOp\Greater($exprGen(), $exprGen());
            $stmts[] = new Stmt\If_($cond, ['stmts' => [$makeAssign()]]);
        }

        // optional loop
        if (ri(0, 1) === 0) {
            if (ri(0, 1) === 0) { // for
                $lv   = 'i' . ri(0, 99);
                $init = [new Expr\Assign(new Expr\Variable($lv), new Node\Scalar\LNumber(0))];
                $cond = [new Expr\BinaryOp\Smaller(new Expr\Variable($lv), new Node\Scalar\LNumber(ri(2, 10)))];
                $step = [new Expr\PostInc(new Expr\Variable($lv))];
                $body = [$makeAssign()];
                $stmts[] = new Stmt\For_(['init'=>$init,'cond'=>$cond,'loop'=>$step,'stmts'=>$body]);
            } else {              // while
                $condExpr = new Expr\BinaryOp\Smaller($exprGen(), $exprGen());
                $body     = [$makeAssign()];
                $stmts[]  = new Stmt\While_($condExpr, $body);
            }
        }
    }

    // return
    $stmts[] = new Stmt\Return_(new Expr\Variable($vars[array_rand($vars)]));

    // wrap & call
    $func = $factory->function('main')->addStmts($stmts)->getNode();
    return (new Printer())->prettyPrintFile([
        $func,
        new Expr\FuncCall(new Node\Name('main'))
    ]);
}

//──────────────────────── I/O + Entrypoint
function write_prog($code, $dir, $i) {
    if (!is_dir($dir) && !mkdir($dir, 0777, true)) die("mkdir failed\n");
    $p = rtrim($dir, '/\\') . "/prog_{$i}.php";
    file_put_contents($p, $code); return $p;
}

function main(array &$built) {
    $o          = opts();
    $easy       = isset($o['easy']);
    $useBuiltin = !isset($o['no-builtin']);

    if (isset($o['seed']) && $o['seed'] !== false) {
        mt_srand((int)$o['seed']); echo "[*] seed {$o['seed']}\n"; }

    if (!isset($o['n']) || isset($o['print'])) {
        echo gen_program($easy, $built, $useBuiltin), "\n"; return; }

    $n   = (int) $o['n'];
    $out = isset($o['out']) && $o['out'] !== false ? $o['out'] : __DIR__ . '/generated';
    echo "[*] generating $n files to $out …\n";
    for ($i = 1; $i <= $n; $i++) {
        echo "[+] " . write_prog(gen_program($easy, $built, $useBuiltin), $out, $i) . "\n"; }
}

main($BUILT_INS);
