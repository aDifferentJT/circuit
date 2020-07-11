module LineDrawing

%default total

public export
data LineStyle
  = None
  | Thin
  | Bold

boldenStyle : LineStyle -> LineStyle
boldenStyle None = None
boldenStyle Thin = Bold
boldenStyle Bold = Bold

public export
record LineDir where
  constructor MkLineDir
  lineN : LineStyle
  lineS : LineStyle
  lineW : LineStyle
  lineE : LineStyle

export
space : LineDir
space = MkLineDir None None None None

export
bolden : LineDir -> LineDir
bolden (MkLineDir n s w e) = MkLineDir (boldenStyle n) (boldenStyle s) (boldenStyle w) (boldenStyle e)

export
lineDrawingChar : LineDir -> Char
lineDrawingChar (MkLineDir None None None None) = ' '

lineDrawingChar (MkLineDir None None Thin Thin) = chr 0x2500
lineDrawingChar (MkLineDir None None Bold Bold) = chr 0x2501

lineDrawingChar (MkLineDir Thin Thin None None) = chr 0x2502
lineDrawingChar (MkLineDir Bold Bold None None) = chr 0x2503

lineDrawingChar (MkLineDir None Thin None Thin) = chr 0x250C
lineDrawingChar (MkLineDir None Thin None Bold) = chr 0x250D
lineDrawingChar (MkLineDir None Bold None Thin) = chr 0x250E
lineDrawingChar (MkLineDir None Bold None Bold) = chr 0x250F

lineDrawingChar (MkLineDir None Thin Thin None) = chr 0x2510
lineDrawingChar (MkLineDir None Thin Bold None) = chr 0x2511
lineDrawingChar (MkLineDir None Bold Thin None) = chr 0x2512
lineDrawingChar (MkLineDir None Bold Bold None) = chr 0x2513

lineDrawingChar (MkLineDir Thin None None Thin) = chr 0x2514
lineDrawingChar (MkLineDir Thin None None Bold) = chr 0x2515
lineDrawingChar (MkLineDir Bold None None Thin) = chr 0x2516
lineDrawingChar (MkLineDir Bold None None Bold) = chr 0x2517

lineDrawingChar (MkLineDir Thin None Thin None) = chr 0x2518
lineDrawingChar (MkLineDir Thin None Bold None) = chr 0x2519
lineDrawingChar (MkLineDir Bold None Thin None) = chr 0x251A
lineDrawingChar (MkLineDir Bold None Bold None) = chr 0x251B

lineDrawingChar (MkLineDir Thin Thin None Thin) = chr 0x251C
lineDrawingChar (MkLineDir Thin Thin None Bold) = chr 0x251D
lineDrawingChar (MkLineDir Bold Thin None Thin) = chr 0x251E
lineDrawingChar (MkLineDir Thin Bold None Thin) = chr 0x251F
lineDrawingChar (MkLineDir Bold Bold None Thin) = chr 0x2520
lineDrawingChar (MkLineDir Bold Thin None Bold) = chr 0x2521
lineDrawingChar (MkLineDir Thin Bold None Bold) = chr 0x2522
lineDrawingChar (MkLineDir Bold Bold None Bold) = chr 0x2523

lineDrawingChar (MkLineDir Thin Thin Thin None) = chr 0x2524
lineDrawingChar (MkLineDir Thin Thin Bold None) = chr 0x2525
lineDrawingChar (MkLineDir Bold Thin Thin None) = chr 0x2526
lineDrawingChar (MkLineDir Thin Bold Thin None) = chr 0x2527
lineDrawingChar (MkLineDir Bold Bold Thin None) = chr 0x2528
lineDrawingChar (MkLineDir Bold Thin Bold None) = chr 0x2529
lineDrawingChar (MkLineDir Thin Bold Bold None) = chr 0x252A
lineDrawingChar (MkLineDir Bold Bold Bold None) = chr 0x252B

lineDrawingChar (MkLineDir None Thin Thin Thin) = chr 0x252C
lineDrawingChar (MkLineDir None Thin Bold Thin) = chr 0x252D
lineDrawingChar (MkLineDir None Thin Thin Bold) = chr 0x252E
lineDrawingChar (MkLineDir None Thin Bold Bold) = chr 0x252F
lineDrawingChar (MkLineDir None Bold Thin Thin) = chr 0x2530
lineDrawingChar (MkLineDir None Bold Bold Thin) = chr 0x2531
lineDrawingChar (MkLineDir None Bold Thin Bold) = chr 0x2532
lineDrawingChar (MkLineDir None Bold Bold Bold) = chr 0x2533

lineDrawingChar (MkLineDir Thin None Thin Thin) = chr 0x2534
lineDrawingChar (MkLineDir Thin None Bold Thin) = chr 0x2535
lineDrawingChar (MkLineDir Thin None Thin Bold) = chr 0x2536
lineDrawingChar (MkLineDir Thin None Bold Bold) = chr 0x2537
lineDrawingChar (MkLineDir Bold None Thin Thin) = chr 0x2538
lineDrawingChar (MkLineDir Bold None Bold Thin) = chr 0x2539
lineDrawingChar (MkLineDir Bold None Thin Bold) = chr 0x253A
lineDrawingChar (MkLineDir Bold None Bold Bold) = chr 0x253B

lineDrawingChar (MkLineDir Thin Thin Thin Thin) = chr 0x253C
lineDrawingChar (MkLineDir Thin Thin Bold Thin) = chr 0x253D
lineDrawingChar (MkLineDir Thin Thin Thin Bold) = chr 0x253E
lineDrawingChar (MkLineDir Thin Thin Bold Bold) = chr 0x253F
lineDrawingChar (MkLineDir Bold Thin Thin Thin) = chr 0x2540
lineDrawingChar (MkLineDir Thin Bold Thin Thin) = chr 0x2541
lineDrawingChar (MkLineDir Bold Bold Thin Thin) = chr 0x2542
lineDrawingChar (MkLineDir Bold Thin Bold Thin) = chr 0x2543
lineDrawingChar (MkLineDir Bold Thin Thin Bold) = chr 0x2544
lineDrawingChar (MkLineDir Thin Bold Bold Thin) = chr 0x2545
lineDrawingChar (MkLineDir Thin Bold Thin Bold) = chr 0x2546
lineDrawingChar (MkLineDir Bold Thin Bold Bold) = chr 0x2547
lineDrawingChar (MkLineDir Thin Bold Bold Bold) = chr 0x2548
lineDrawingChar (MkLineDir Bold Bold Bold Thin) = chr 0x2549
lineDrawingChar (MkLineDir Bold Bold Thin Bold) = chr 0x254A
lineDrawingChar (MkLineDir Bold Bold Bold Bold) = chr 0x254B

lineDrawingChar (MkLineDir None None Thin None) = chr 0x2574
lineDrawingChar (MkLineDir Thin None None None) = chr 0x2575
lineDrawingChar (MkLineDir None None None Thin) = chr 0x2576
lineDrawingChar (MkLineDir None Thin None None) = chr 0x2577
lineDrawingChar (MkLineDir None None Bold None) = chr 0x2578
lineDrawingChar (MkLineDir Bold None None None) = chr 0x2579
lineDrawingChar (MkLineDir None None None Bold) = chr 0x257A
lineDrawingChar (MkLineDir None Bold None None) = chr 0x257B
lineDrawingChar (MkLineDir None None Thin Bold) = chr 0x257C
lineDrawingChar (MkLineDir Thin Bold None None) = chr 0x257D
lineDrawingChar (MkLineDir None None Bold Thin) = chr 0x257E
lineDrawingChar (MkLineDir Bold Thin None None) = chr 0x257F

export
flipV : LineDir -> LineDir
flipV d = record {lineN = lineS d, lineS = lineN d} d

