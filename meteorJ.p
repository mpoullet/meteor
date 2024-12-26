program meteor(input, output, magfile, coefile);
{ version I: Wed Jun 27 13:36:06 EDT 1990 }

{ copyright Prof. K. Steiglitz
	    Dept. of Computer Science
	    Princeton University
	    Princeton, NJ 08544 }

{ Constraint-based design of linear-phase fir filters with
  upper and lower bounds, and convexity constraints.
  Finds minimum length, or optimizes fixed length, or pushes band-edges.
  If L is the filter length, the models are

  odd-length
   cosine:   sum ( i from 0 to (L-1)/2 ) coeff[i]*cos(i*omega)
   sine:     sum ( i from 0 to (L-3)/2 ) coeff[i]*sin((i+1)*omega)

  even-length
   cosine:   sum ( i from 0 to L/2-1 ) coeff[i]*cos((i+.5)*omega)
   sine:     sum ( i from 0 to L/2-1 ) coeff[i]*sin((i+.5)*omega)  }

  const
    maxpivots = 1000;   { maximum no. of pivots }
    small = 1.0e-8;     { small number used in defining band-edges }
    large = 1.0e+31;    { large number used in search for minimum cost column }
    mmax = 64;          { max. no. of coefficients }
    Lmax = 129;         { max. filter length, L = 2*m-1, 2*m, or 2*m+1 }
    mmaxm = 63;         { mmax - 1 }
    nmax = 640;         { max. size of n, where there are n+1 grid-points }
    ncolmax = 6000;     { max. no. of columns allowed in tableau }
    nspecmax = 20;      { max. no. of specifications }
    eps = 1.0e-8;       { for testing for zero }

  var
    magfile, coefile: file of char;  { files for output }
    done, unbounded, optimal: boolean;          { flags for simplex }
    result: (toomanycols, unbdual, infdual, toomanypivots, opt,
	     infprimal);                        { result of simplex }
    iteration: integer;      { iteration count, index }
    ch: char;                   { character for input }
    m: 1..mmax;         { no. of coefficients, left and right half m }
    L: 1..Lmax;         { filter length = 2*m-1, 2*m, 2*m+1 }
    n: 1..nmax;         { there are n+1 grid-points from 0 to pi }
    numpivots: integer; { pivot count }
    pivotcol, pivotrow: integer;        { pivot column and row }
    pivotel: real;                      { pivot element }
    pi: real;           { 3.14159265358979... }
    cbar: real;         { price when searching for entering column }
    coeff: array[0..mmaxm] of real;     { coefficients }
    carry: array[-1..mmax, -1..mmax] of real;   { inverse-basis matrix of the
						  revised simplex method }
    phase: 1..2;        { phase }
    price: array[0..mmax] of real;      { shadow prices = row -1 of carry =
					  -dual variables = -coefficients }
    basis: array[0..mmax] of integer;  { basis columns, negative integers
					  artificial }
    nspec: 0..nspecmax;                 { no. of bands }
    spectype: array[1..nspecmax] of (con, lim);
						{ type of band }
    left, right: array[1..nspecmax] of real;    { bandedges as read in }
    freq: array[1..ncolmax] of real;            { frequencies at grid points }
    bound1, bound2:  array[1..nspecmax] of real;{ left and right bounds }
    sense: array[1..nspecmax] of char;  { sense of constraint, + up, - down }
    interpolate: array[1..nspecmax] of char; { g=geometric, a=arithmetic }
    firstcol: array[1..nspecmax] of 1..ncolmax; { leftmost column of spec }
    lastcol: array[1..nspecmax] of 1..ncolmax;  { rightmost column of spec }
    foundfeas: boolean;                 { found feasible solution }
    mlargest, msmallest: integer;       { range of m }
    Llargest, Lsmallest: integer;       { range of L = 2*m-1, 2*m, or 2*m+1 }
    ncol: 1..ncolmax;                   { number of columns }
    tab: array[0..mmax, 1..ncolmax] of real;    { tableau }
    d: array[1..ncolmax] of real;       { current cost vector }
    c: array[1..ncolmax] of real;       { cost in original problem }
    curcol: array[-1..mmax] of real;    { current column }
    curcost: real;                      { current cost }
    bestm: integer;     { best order }
    hug: array[1..nspecmax] of char;    { allow this constraint to be hugged? }
    whattodo: (findlen, maxdist, pushedge);   { type of optimization }
    npushed: integer;   { number of bandedges pushed }
    whichway: (rr, ll); { push which way? }
    bandpushed: array[1..nspecmax] of integer;  {  bandedges pushed }
    lowlim: real;       { lower limit for finding if primal is feasible }
    oddlength: boolean; { odd-length filters? }
    symtype: (cosine, sine);    { cosine or sine symmetry }

procedure makebands(i: integer);
{ fills in frequencies to make grid - frequencies are kept as reals
  in radians, and each band has equally spaced grid points }

var
  k, kmax: integer;

begin { makebands }
  if( i = 1 ) then firstcol[i]:= 1 else firstcol[i]:= lastcol[i-1] + 1;
  kmax:= trunc((right[i]-left[i])*n/0.5+small);{ kmax+1 cols. in this band }
  if( kmax = 0 ) then  freq[firstcol[i]]:= 2.0*pi*left[i]
    else
      for k:= 0 to kmax do
	  freq[firstcol[i]+k]:= 2.0*pi*(left[i] + (right[i]-left[i])*k/kmax);
  lastcol[i]:= firstcol[i] + kmax
end;  { makebands }


function trig0(i: integer; f:real): real;
{ trig function in filter transfer function }

begin { trig0 }
 if oddlength then
  if (symtype = cosine) then
   trig0:= cos(i*f)
  else
   trig0:= sin((i+1)*f);

 if (not oddlength) then
  if (symtype = cosine) then
   trig0:= cos((i+0.5)*f)
  else
   trig0:= sin((i+0.5)*f)

end;  { trig0 }

function trig2(i: integer; f: real): real;
{ second derivative of trig function in filter transfer function }

begin { trig2 }
 if oddlength then
  if (symtype = cosine) then
   trig2:= -i*i*cos(i*f)
  else
   trig2:= -(i+1)*(i+1)*sin((i+1)*f);

 if (not oddlength) then
  if (symtype = cosine) then
   trig2:= -(i+0.5)*(i+0.5)*cos((i+0.5)*f)
  else
   trig2:= -(i+0.5)*(i+0.5)*sin((i+0.5)*f)

end;  { trig2 }

procedure convex(i: integer);
{ sets up tableau columns for convexity constraints on magnitude }

  var
    row, col: integer;       { gridpoint, side of polygon, row, col }

  begin  { convex }
    makebands(i);
    for col:= firstcol[i] to lastcol[i] do      { for all frequencies in band }
	begin
	  c[col]:= 0.0;
	  for row:= 0 to (m-1) do
	    begin
	      tab[row, col]:=   { normal constraint is <= }
		trig2(row, freq[col]);
	      if( sense[i] = '+' ) then tab[row, col]:= -tab[row, col]
	    end;  { for row }
	  tab[m, col]:= 0.0
	end  {for col }
end;   { convex }


procedure limit (i: integer);
{ sets up tableau columns for upper or lower bounds on transfer
  function for specification i; the bound is linearly interpolated
  between the start and end of the band }

  var
    row, col: integer;       { gridpoint, side of polygon, row, col }

  begin  { limit }
    makebands(i);
    for col:= firstcol[i] to lastcol[i] do  { for all frequencies in band }
	begin
	  if( firstcol[i] = lastcol[i] ) then c[col]:= bound1[i]
	    else
	      begin
		if( interpolate[i] = 'g' ) then c[col]:=
		  bound1[i]*exp( ((col-firstcol[i])/(lastcol[i]-firstcol[i]))
			   *ln(abs(bound2[i]/bound1[i])) );
		if( interpolate[i] = 'a' ) then c[col]:=
		  bound1[i] + ((col-firstcol[i])/(lastcol[i]-firstcol[i])
			   *(bound2[i]-bound1[i]) )
	      end;
	  if( sense[i] = '-' ) then c[col]:= -c[col];
	  for row:= 0 to (m-1) do
	    begin
	     tab[row, col]:= trig0(row, freq[col]);
	     if( sense[i] = '-' ) then tab[row, col]:= -tab[row, col]
	    end;
	  if ( hug[i] <> 'h' )  then  tab[m, col]:= 1.0
				else  tab[m, col]:= 0.0
	end  { for col }
end;   { limit }


procedure readdata;
{ reads in problem data }
{ not meant to be interactive; aborts on bad filter lengths}

var
  i: integer;
  allhugged: boolean;   { to see if all constraints are hugged }

begin  { readdata }
  readln(Lsmallest, Llargest);

  if ( ( Lsmallest < 1 ) or (Llargest > Lmax) ) then
   begin
    writeln('Lsmallest or Llargest out of range: quitting');
    halt
   end;

  if ( odd(Lsmallest) <> odd(Llargest) ) then
   begin
    writeln('parity of Lsmallest and Llargest unequal: quitting');
    halt
   end;

  readln(ch);
  if(ch = 'c') then symtype:= cosine
	       else symtype:= sine;
  if(symtype = cosine) then writeln('cosine symmetry')
		       else writeln('sine symmetry');

  oddlength:= odd(Lsmallest);

  if oddlength then
   if (symtype = cosine) then
    begin
     msmallest:= (Lsmallest + 1) div 2;
     mlargest := (Llargest  + 1) div 2
    end
   else
    begin
     msmallest:= (Lsmallest - 1) div 2;
     mlargest := (Llargest  - 1) div 2
    end;

  if not oddlength then
   begin
    msmallest:= Lsmallest div 2;
    mlargest := Llargest  div 2
   end;

  if( Lsmallest <> Llargest ) then
    begin
      whattodo:= findlen;
      writeln('finding minimum length: range ',
	       Lsmallest:4, ' to ', Llargest:4)
    end;

  if( Lsmallest = Llargest ) then
    begin
      m:= msmallest;
      L:= Lsmallest;
      writeln('fixed length of ', L:4);
      readln(ch);     { right, left, or neither: edges to be pushed? }
      if( ch = 'n' ) then
	begin
	  whattodo:= maxdist;
	  writeln('maximizing distance from constraints not marked hugged')
	end
      else
	begin
	  whattodo:= pushedge;
	  if( ch = 'r' ) then whichway:= rr else whichway:= ll;
	  readln(npushed);
	  for i:= 1 to npushed do read(bandpushed[i]);
	  readln;
	  if( whichway = rr ) then writeln('pushing bandedges right');
	  if( whichway = ll ) then writeln('pushing bandedges left');
	  write('constraint numbers: ');
	  for i:= 1 to npushed do write(bandpushed[i]:3, ' ');
	  writeln
	end;
      end;
    readln(n);  { there are n+1 grid points between 0 and pi }
    nspec:= 0;
    readln(ch);
    while( ch <> 'e' ) do   { 'e' for end }
      begin
	nspec:= nspec + 1;
	i:= nspec;
	if( ch = 'c') then
	  begin
	    spectype[i]:= con;
	    readln( sense[i] );
	    readln( left[i], right[i] );
	    writeln('constraint ', i:1, ': convex, sense ', sense[i]);
	    writeln('  bandedges:  ', left[i]:10:4, ' ', right[i]:10:4)
	  end;
	if( ch = 'l') then
	  begin
	    spectype[i]:= lim;
	    readln( sense[i] );
	    readln( interpolate[i] );
	    readln( hug[i] );
	    readln( left[i], right[i] );
	    readln( bound1[i], bound2[i] );
	    if( (interpolate[i] = 'g') and (bound1[i]*bound2[i]=0.0) ) then
	      begin
		writeln('geometrically interpolated bandedge in constraint ',
			 i:5, ' is zero');
		halt
	      end;
	    if( sense[i] = '+' ) then
	      writeln('constraint ', i:2, ': upper limit');
	    if( sense[i] = '-' ) then
	      writeln('constraint ', i:2, ': lower limit');
	    if( interpolate[i] = 'g' ) then
	      writeln('  geometric interpolation');
	    if( interpolate[i] = 'a' ) then
	      writeln('  arithmetic interpolation');
	    if( hug[i] = 'h' )
	      then  writeln('  this constraint will be hugged')
	      else  writeln('  this constraint will be optimized');
	    writeln('  bandedges:  ', left[i]:10:4, ' ', right[i]:10:4);
	    writeln('  bounds:     ', bound1[i]:10:4, ' ', bound2[i]:10:4)
	  end;
	makebands(i);
	writeln('  initial columns:    ', firstcol[i]:10, ' ', lastcol[i]:10);
	readln(ch)  { next }
      end;  { while }
    ncol:= lastcol[nspec];
    writeln('number of specs= ', nspec:5);
    writeln('initial number of columns= ', ncol:5);

    allhugged:= true;   { check to see if all limit constraints are hugged }
    for i:= 1 to nspec do
     if (spectype[i] = lim) and (hug[i] <> 'h') then
      allhugged:= false;
    if allhugged then
     begin
      writeln('all constraints are hugged: ill-posed problem');
      halt
     end

  end;   { readdata }


procedure setup;
{ initializes constraints }

var
  i: integer;

begin  { setup }
  pi:= 4.0*arctan(1.0);
  for i:= 1 to nspec do
    begin
      case spectype[i] of
	con: convex(i);
	lim: limit(i)
      end  { case }
  end;  {for }
  ncol:= lastcol[nspec]
end;   { setup }


procedure columnsearch;
{ looks for favorable column to enter basis.
  returns lowest cost and its column number, or turns on the flag optimal }

var
  i, col: integer;
  tempcost: real;           { minimum cost, temporary cost of column }

  begin  { columnsearch }
    for i:= 0 to m do price[i]:= -carry[-1, i];  { set up price vector }
    optimal:= false;
    cbar:= large;
    pivotcol:= 0;
    for col:= 1 to ncol do
      begin
	tempcost:= d[col];
	for i:= 0 to m do tempcost:= tempcost - price[i]*tab[i, col];
	if( cbar > tempcost ) then
	  begin
	   cbar:= tempcost;
	   pivotcol:= col
	  end
      end;  { for col }
    if ( cbar > -eps ) then optimal:= true
  end;   { columnsearch }


procedure rowsearch;
{  looks for pivot row. returns pivot row number,
   or turns on the flag unbounded }

var
  i, j: integer;
  ratio, minratio: real;        { ratio and minimum ratio for ratio test }

  begin  { rowsearch }
    for i:= 0 to m do           { generate column }
      begin
	curcol[i]:= 0.0;        { current column = B inverse * original col. }
	for  j:= 0 to m do curcol[i]:=
			   curcol[i] + carry[i, j]*tab[j, pivotcol]
      end;
  curcol[-1]:= cbar;            { first element in current column }
  pivotrow:= -1;
  minratio:= large;
  for i:= 0 to m do                             { ratio test }
    begin
      if( curcol[i] > eps ) then
	begin
	  ratio:= carry[i, -1]/curcol[i];
	    if( minratio > ratio ) then         { favorable row }
	      begin
		minratio:= ratio;
		pivotrow:= i;
		pivotel:= curcol[i]
	      end
	    else { break tie with max pivot }
	      if ( (minratio = ratio) and (pivotel < curcol[i]) ) then
		  begin
		    pivotrow:= i;
		    pivotel:= curcol[i]
		  end
	end  { curcol > eps }
      end;  { for i }
    if ( pivotrow = -1 ) then  unbounded:= true         { nothing found }
			 else  unbounded:= false
  end;  { rowsearch }


procedure pivot;
{ pivots }

  var
    i, j: integer;

  begin { pivot }
    basis[pivotrow]:= pivotcol;
    for j:= -1 to m do carry[pivotrow, j]:= carry[pivotrow, j]/pivotel;
    for i:= -1 to m do
      if( i<> pivotrow ) then
	for j:= -1 to m do
	  carry[i, j]:= carry[i, j] - carry[pivotrow, j]*curcol[i];
    curcost:= -carry[-1, -1]
  end;  { pivot }


procedure changephase;
{ changes phase from 1 to 2, by switching to original cost vector }

  var
    i, j, b: integer;

  begin  { changephase }
    phase:= 2;
    for i:= 0 to m do if( basis[i] <= 0 ) then
      writeln( '...artificial basis element ', basis[i]:5,
	       ' remains in basis after phase 1');
    for j:= 1 to ncol do d[j]:= c[j];   { switch to original cost vector }
    for j:= -1 to m do
      begin
	carry[-1, j]:= 0.0;
	for i:= 0 to m do
	  begin
	    b:= basis[i];       { ignore artificial basis elements that are }
	    if( b >= 1 ) then   { still in basis }
	      carry[-1, j]:= carry[-1, j] - c[b]*carry[i,j]
	  end  { for i }
      end;  { for j }
    curcost:= -carry[-1, -1]
  end;   { changephase }

function mag( f: real ): real;
{ computes magnitude function, given radian frequency f }

var
  i: integer;
  temp: real;

begin  { mag }
  temp:= 0.0;
  for i:= 0 to (m-1) do
      temp:= temp + coeff[i]*trig0(i,f);
  mag:= temp
end;  { mag }


procedure wrapup;
{ prints results, final frequency response }

var
  i, k: integer;

  begin  { wrapup }
    rewrite( magfile, "magfile" );         { open files for writing }
    rewrite( coefile, "coefile" );

    if (oddlength and (symtype = cosine)) then  { write coeffs to coefile }
     begin
      writeln(coefile, 2*m-1:4, ' cosine symmetry');    { L = length, odd }
      for i:= (m-1) downto 1 do
       writeln(coefile, coeff[i]/2);
      writeln(coefile, coeff[0]);
      for i:= 1 to (m-1) do
       writeln(coefile, coeff[i]/2)
     end;       { odd, cosine }

    if ((not oddlength) and (symtype = cosine)) then
     begin
      writeln(coefile, 2*m:4, ' cosine symmetry');      { L = length, even }
      for i:= (m-1) downto 0 do
       writeln(coefile, coeff[i]/2);
      for i:= 0 to (m-1) do
       writeln(coefile, coeff[i]/2)
     end;       { even, cosine }

    if (oddlength and (symtype = sine)) then
     begin
      writeln(coefile, 2*m+1:4, ' sine symmetry');      { L = length, odd }
      for i:= (m-1) downto 0 do
       writeln(coefile, -coeff[i]/2);   { negative of the first m coefs. }
       writeln(coefile, ' 0.0');        { middle coefficient is always 0 }
      for i:= 0 to (m-1) do
       writeln(coefile, coeff[i]/2)
     end;       { odd, sine }

    if ((not oddlength) and (symtype = sine)) then
     begin
      writeln(coefile, 2*m:4, ' sine symmetry');        { L = length, even }
      for i:= (m-1) downto 0 do
       writeln(coefile, -coeff[i]/2);   { negative of the first m coefs. }
      for i:= 0 to (m-1) do
       writeln(coefile, coeff[i]/2)
     end;       { even, sine }

    for k:= 0 to n do      { magnitude on regular grid }
	writeln( magfile, 0.5*k/n:10:4, ' ', mag( k*pi/n) );
    writeln( magfile );
    writeln( magfile, '       magnitude at bandedges');
    writeln( magfile );
    for i:= 1 to nspec do
      if( spectype[i] = lim ) then
	begin
	  writeln( magfile, freq[firstcol[i]]*0.5/pi:10:4, ' ',
		   mag( freq[firstcol[i]] ) );
	  writeln( magfile, freq[lastcol[i]]*0.5/pi:10:4, ' ',
		   mag( freq[lastcol[i]]  ) );
	  writeln
	end
  end;   { wrapup }


procedure simplex;
{ simplex for linear programming }

var
  i, j, col, row: integer;

begin  { simplex }
  done:= false;
  phase:= 1;
  for i:= -1 to m do for j:= -1 to mmax do carry[i, j]:= 0.0;
  for i:= 0 to m do carry[i, i]:= 1.0;        { artificial basis }
  carry[-1, -1]:= -1.0;                       { - initial cost }
  curcost:= -carry[-1, -1];
  carry[ m, -1]:= 1.0;                        { variable minimized in primal }
  for i:= 0 to m do basis[i]:= -i;            { initial, artificial basis }
  if( ncol <= ncolmax ) then    { check number of columns }
    for col:= 1 to ncol do      { initialize cost for phase 1 }
      begin
	d[col]:= 0.0;
	for row:= 0 to m do d[col]:= d[col] - tab[row, col]
      end
  else
    begin
      writeln('...termination: too many columns for storage');
      done:= true;
      result:= toomanycols
    end;
  numpivots:= 0;
  while( (numpivots < maxpivots) and (not done) and
	 ( (curcost > lowlim) or (phase = 1) ) ) do
    begin
      columnsearch;
      if( not optimal ) then
	begin                         { not optimal }
	  rowsearch;
	    if( unbounded ) then
	      begin
		done:= true;
		result:= unbdual        { dual of problem is unbounded }
	      end
	    else
	      begin
		pivot;
		numpivots:= numpivots + 1;
		if ( (numpivots = 1 ) or ( numpivots mod 10 = 0 ) ) then
		      writeln('pivot ', numpivots:4, ' cost= ', curcost:12)
	      end
	end  { not optimal }
      else                            { optimal }
	  if( phase = 1 ) then
	    begin
	      if( curcost > eps ) then
		begin
		  done:= true;     { dual of problem is infeasible }
		  result:= infdual { this happens if all specs are hugged }
		end
	      else
		begin
		  if ( (numpivots <> 1 ) and ( numpivots mod 10 <> 0 ) ) then
		    writeln('pivot ', numpivots:4, ' cost= ', curcost:12);
		  writeln('phase 1 successfully completed');
		  changephase
		end
	    end  { if phase = 1 }
	  else
	    begin
	      if ( (numpivots <> 1 ) and ( numpivots mod 10 <> 0 ) ) then
		writeln('pivot ', numpivots:4, ' cost= ', curcost:12);
	      writeln('phase 2 successfully completed');
	      done:= true;
	      result:= opt
	    end
    end;  { while }
  if( (curcost <= lowlim) and (phase = 2) ) then
    begin
      if ( (numpivots <> 1 ) and ( numpivots mod 10 <> 0 ) ) then
	writeln('pivot ', numpivots:4, ' cost= ', curcost:12);
      result:= infprimal
    end;
  if ( numpivots >= maxpivots ) then
    begin
      writeln('...termination: maximum number of pivots exceeded');
      result:= toomanypivots
    end
end;  { simplex }

procedure printresult;
{ prints enumerated type }

begin
  case result of
    toomanycols: writeln('too many columns in specifications');
    unbdual: writeln('infeasible (unbounded dual)');   { unbounded dual }
    infdual: writeln('infeasible or unbounded');{ infeasible dual }
    toomanypivots: writeln('too many pivots');
    opt: writeln('optimum obtained');
    infprimal: writeln('infeasible ')
  end { case }
end; { printresult }

procedure getm;
{ find best order (and hence length) }

var
  leftm, rightm: 1..mmax;
  i: integer;
  foundm, checkedleft, checkedright: boolean;

begin  { getm }
  foundfeas:= false;  { flag set when a feasible solution is found }
  iteration:= 0;
  leftm:= msmallest;
  rightm:= mlargest;
  foundm:= false;
  checkedleft:= false;
  checkedright:= false;
  while ( not foundm ) do
    begin
      if (iteration=0) then
       m:= leftm + (rightm - leftm) div 2;     { first time through }
      iteration:= iteration + 1; 
      writeln;
      writeln('iteration ', iteration:2);

      if oddlength then
       if (symtype = cosine) then
	writeln('L= ', 2*m-1:4)
       else
	writeln('L= ', 2*m+1:4);

      if not oddlength then
	writeln('L= ', 2*m:4);

      setup;
      simplex;
      printresult;
      if( result = opt ) then
	begin
	  foundfeas:= true;
	  rightm:= m;
	  bestm:= m;
          checkedright:= true;  { right side of bracket has been checked }
	  if oddlength then
	   if (symtype = cosine) then
	    writeln('new best length L= ', 2*bestm-1:4)
	   else
	    writeln('new best length L= ', 2*bestm+1:4);

	  if not oddlength then
	   writeln('new best length L= ', 2*bestm:4);

	  for i:= 0 to (m-1) do  coeff[i]:= -carry[-1, i]
	end;

      if( result <> opt ) then 
       begin
        leftm:= m;
        checkedleft:= true  { left side of bracket has been checked }
       end;

      if (rightm > leftm + 1) then
       m:= leftm + (rightm - leftm) div 2;

      if (rightm = leftm + 1) then
       if (not checkedleft) then
        begin
         m:= leftm;
         checkedleft:= true
        end
         else if (not checkedright) then
          begin
           m:= rightm;
           checkedright:= true
          end
            else
             foundm:= true;

      if (rightm = leftm) then
       foundm:= true

    end;  { while }

  if( not foundfeas ) then
    begin
      writeln('no feasible solution found');
      halt
    end;
  m:= bestm;

  writeln;
  if oddlength then
   if (symtype = cosine) then
    writeln('best length L= ', 2*bestm-1:4)
   else
    writeln('best length L= ', 2*bestm+1:4);

  if not oddlength then
   writeln('best length L= ', 2*bestm:4)

end;  { getm }

procedure getedge;
{ optimize bandedge }

var
  lefte, righte, newe, beste: real;
  onespace, stopspace: real; { nominal grid spacing, stop criterion }
  i: integer;

begin { getedge }
  onespace:= 0.5/n;     { space between grid points }
  stopspace:= onespace/10.0;    { stop criterion is 1/10 nominal grid spacing }
  if( whichway = rr ) then
    begin
      lefte:= left[bandpushed[1]];      { start with rightmost leftedge }
      for i:= 2 to npushed do
	if( left[bandpushed[i]] > lefte ) then lefte:= left[bandpushed[i]];
      righte:= 0.5
    end
  else
    begin
      lefte:= 0.0;
      righte:= right[bandpushed[1]];
      for i:= 2 to npushed do   { start with leftmost rightedge }
	if( right[bandpushed[i]] < righte ) then righte:= right[bandpushed[i]]
    end;
  iteration:= 0;
  foundfeas:= false;  { flag set when a feasible solution is found }
  while( (righte - lefte) > stopspace ) do
    begin
      iteration:= iteration + 1;
      newe:= (righte + lefte)/2.0;
      writeln;
      writeln('iteration ', iteration:4);
      writeln('trying new edge = ', newe:10:4);
      for i:= 1 to npushed do
	if( whichway = rr ) then right[bandpushed[i]]:= newe
			    else left [bandpushed[i]]:= newe;
      setup;
      simplex;
      printresult;
      if( result = opt ) then
	begin
	  if( whichway = rr ) then  lefte:= newe
			      else righte:= newe;
	  foundfeas:= true;
	  beste:= newe;
	  for i:= 0 to (m-1) do  coeff[i]:= -carry[-1, i]
	end;
      if( result <> opt ) then
	if( whichway = rr ) then righte:= newe
			    else  lefte:= newe
    end; { while }
  writeln;
  if( not foundfeas ) then
    begin
      writeln('no feasible bandedge found');
      halt
    end;
  writeln('found edge= ', beste:10:4);
  for i:= 1 to npushed do
      if( whichway = rr ) then right[bandpushed[i]]:= beste
			  else  left[bandpushed[i]]:= beste;
  for i:= 1 to nspec do  makebands(i);
end;  { getedge }


procedure getmaxdist;
{ maximizes distance from constraints }

var
  i: integer;

begin  { getmaxdist }
  writeln('optimization: maximize distance from constraints');
  setup;
  simplex;
  printresult;
  if( result = opt ) then
   begin
    writeln('final cost= distance from constraints= ', curcost:12);
    for i:= 0 to (m-1) do     { record coefficients }
     coeff[i]:= -carry[-1, i]
   end
  else
   halt                 { don't go back if unsuccessful }
end;  { getmaxdist }


begin  { main }
  writeln('welcome to meteor:');
  writeln('constraint-based, linear-phase FIR filter design');
  readdata;
  lowlim:= -eps;        { dual cost negative => primal infeasible }
  case whattodo of
      findlen: getm;
      pushedge:  getedge;
      maxdist:   getmaxdist
    end; { case }       { no return here if unsuccessful }
  wrapup
end.  { main }

