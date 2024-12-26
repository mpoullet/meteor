program form(input, output);
{ version H: Sun Oct 16 03:27:50 EDT 1988 }

{ copyright Prof. K. Steiglitz
	    Dept. of Computer Science
	    Princeton University
	    Princeton, NJ 08544 }

{ generates input file for meteor }

{ Constraint-based design of linear-phase fir filters with
  upper and lower bounds, and convexity constraints.
  Finds minimum length, or optimizes fixed length, or pushes band-edges.
  If L is the filter length, the models are

  odd-length
   cosine:   sum ( i from 0 to (L-1)/2 ) coeff[i]*cos(i*omega)
   sine:     sum ( i from 0 to (L-1)/2 ) coeff[i]*sin((i+1)*omega)

  even-length
   cosine:   sum ( i from 0 to L/2-1 ) coeff[i]*cos((i+.5)*omega)
   sine:     sum ( i from 0 to L/2-1 ) coeff[i]*sin((i+.5)*omega)  }

const
  Lmax = 128;           { filter length }
  nspecmax = 20;        { max. no. of specifications }
  maxnamelength = 10;   { max. length of output file name }

type
  name = packed array [1..maxnamelength] of char;

var
  infile, outfile: text;
  infilename, outfilename: name;
  ch: char;
  gotwhattodo: boolean; { remembers if we've gotten whattodo }
  Lsmallest, Llargest: 1..Lmax;
  n: integer;           { there are n+1 columns from 0 to pi }
  i: integer;
  result: array[1..nspecmax] of real;
  whichway: (ll, rr);
  nspec: 0..nspecmax;   { no. of bands }
  spectype: array[1..nspecmax] of (con, lim);   { type of band }
  left, right: array[1..nspecmax] of real;      { bandedges as read in }
  bound1, bound2:  array[1..nspecmax] of real;  { left and right bounds }
  sense: array[1..nspecmax] of char;    { sense of constraint, + up, - down }
  interpolate: array[1..nspecmax] of char;      { g=geometric, a=arithmetic }
  hug: array[1..nspecmax] of char;      { allow this constraint to be hugged? }
  whattodo: (findlen, maxdist, pushedge);     { type of optimization }
  npushed: integer;                             { number of bandedges pushed }
  bandpushed: array[1..nspecmax] of integer;    { bandedges pushed }
  ok: boolean;                                  { flag to get good input }
  symtype: (cosine, sine);                      { cosine or sine model }

procedure getnum (nnum: integer);

{ finds the first nnum fixed-point numbers in input
  line, puts the numbers in the array called result }

const
  maxlinelen= 250;
  zero= '0';
  nine= '9';
  point=  '.';
  blank= ' ';
  plus= '+';
  minus= '-';
  radix= 10.0;

type
  buffer= array [1..maxlinelen] of char;

var
  sign, count: integer;
  state: 0..6;
  scalefactor: real;
  length, pos: integer;
  ch: char;
  line: buffer;
  digit, invalid, done: boolean;


procedure getline( var line: buffer; var length: integer; var infile: text);
{ reads a line into buffer }

var
  ch: char;

begin  { getline }
  length:=0;
  while not eoln(infile) do
    begin
      read(infile, ch);
      if length < maxlinelen then
	begin
	  length:=length+1;
	  line[length]:=ch
	end
    end;
  readln(infile)
end;  { getline }


procedure scan( var r: real; var i: integer );
{ scans line buffer for a number r, starting at position i+1 }

begin  { scan }
  state:= 0;
  sign:= 1;
  while( ( i < length ) and ( state < 5 ) ) do  { finite-state machine }
    begin                                       { to recognize numbers }
      i:= i + 1;
      ch:= line[i];
      digit:= ( zero <= ch ) and ( ch <= nine );
      case state of
	0: if( digit ) then
	     begin
	       r:= ord(ch) - ord(zero);
	       state:= 1
	     end
	   else
	   if( ( ch = plus ) or ( ch = minus ) ) then
	     begin
	       if( ch = minus ) then sign:= -1;
	       state:= 2
	     end
	   else
	   if( ch = point ) then
	     begin
	       scalefactor:= radix;
	       state:= 4
	     end
	   else
	   if( ch = blank ) then state:= 0
	   else state:= 5;
	 1: if digit then
	      r:= r*radix + ord(ch)-ord(zero)
	    else
	    if( ch = point ) then
	      begin
		scalefactor:= radix;
		state:= 3
	      end
	    else
	    if( ch = blank ) then
	      state:= 6
	    else state:= 5;
	 2: if( digit ) then
	      begin
		r:= ord(ch)-ord(zero);
		state:= 1
	      end
	    else
	    if( ch = point ) then
	      begin
		scalefactor:= radix;
		state:= 4
	      end
	    else state:= 5;
	 3: if ( digit ) then
	      begin
		r:= r + (ord(ch)-ord(zero))/scalefactor;
		scalefactor:= scalefactor*radix
	      end
	    else if( ch = blank ) then state:= 6
	    else state:= 5;
	  4: if( digit ) then
	       begin
		 r:= (ord(ch)-ord(zero))/scalefactor;
		 scalefactor:= scalefactor*radix;
		 state:= 3
	       end
	     else state:= 5
      end
    end;
  case state of
    0, 2, 4, 5: invalid:= true;
    1, 3, 6:    r:= sign*r
  end;
end;  { scan }


begin  { getnum }
  done:= false;
  while ( not done ) do
    begin
      getline(line, length, input);
      count:= 1;
      invalid:= false;
      pos:= 0;
      while( ( count <= nnum ) and ( not invalid ) ) do
	begin
	  scan( result[count], pos );
	  if( not invalid ) then
	    begin
	      count:= count + 1;
	      if( count > nnum ) then done:= true
	    end
	  else
	    writeln('input not valid, please try again')
	end
  end
end;  { getnum }

procedure getspec(i: integer);
{ reads in data for one spec }

begin  { getspec }
  writeln;
  writeln('       reading data for spec ', i:3);
  writeln('enter "l" for a limit spec, "c" for a convexity spec');
  readln(ch);
  if( ch = 'c' ) then
    begin
      spectype[i]:= con;
      writeln('enter "+" for convex up, "-" for down');
      readln( sense[i] );
      writeln('enter left and right band edges');
      getnum( 2 );
      left[i]:= result[1];
      right[i]:= result[2]
    end;
  if( ch = 'l') then
    begin
      spectype[i]:= lim;
      writeln('enter "+" for upper limit, "-" for lower');
      readln( sense[i] );
      writeln('enter "a" for arithmetic interpolation, "g" for geometric');
      readln( interpolate[i] );
      writeln('enter "h" if this constraint can be hugged/ "n" otherwise');
      readln( hug[i] );
      writeln('enter left and right band edges');
      getnum( 2 );
      left[i]:= result[1];
      right[i]:= result[2];
      writeln('enter bounds at left and right band edges');
      getnum( 2 );
      bound1[i]:= result[1];
      bound2[i]:= result[2]
    end;
end;  { getspec }


procedure writefile;
{ writes data to outfile }

begin  {writefile }
  writeln(outfile, Lsmallest, Llargest, '     smallest and largest length');

  if (symtype = cosine) then
   writeln(outfile, 'c') else writeln(outfile, 's');

  if( whattodo = pushedge ) then
    begin
      if( whichway = ll ) then
	writeln(outfile, 'left     direction of pushed specs')
	  else writeln(outfile, 'right     direction of pushed specs');
      writeln(outfile, npushed, '     number of specs pushed');
      for i:= 1 to npushed do write(outfile, bandpushed[i]);
      writeln(outfile, '     specs pushed')
    end;
  if( whattodo = maxdist ) then
    writeln(outfile,
	    'neither left nor right: maximize distance from constraints');
  writeln(outfile, n, '     number of grid points');
  for i:= 1 to nspec do
    begin
      if( spectype[i] = con ) then
	writeln(outfile, 'convex spec') else writeln(outfile, 'limit spec');
      if( spectype[i] = lim ) then
	if( sense[i] = '+' ) then writeln(outfile, '+     upper limit')
			     else writeln(outfile, '-     lower limit');
      if( spectype[i] = con ) then
	if( sense[i] = '+' ) then writeln(outfile, '+     convex up')
			     else writeln(outfile, '-     convex down');
      if( spectype[i] = lim) then
	if( interpolate[i] = 'a' ) then
	  writeln(outfile, 'arithmetic interpolation')
	    else writeln(outfile, 'geometric interpolation');
      if( spectype[i] = lim) then
	if( hug[i] = 'h' ) then writeln(outfile, 'hugged spec')
			   else writeln(outfile, 'not hugged spec');
      writeln(outfile, left[i], right[i], '     band edges');
      if( spectype[i] = lim) then writeln(outfile, bound1[i], bound2[i], '     bounds')
    end;
  writeln(outfile, 'end')
end;  { writefile }


procedure getfilename( var filename: name);
{ gets name of output file }

var
  length: 0..maxnamelength;

begin  { getfilename }
  length:=0;
  while not eoln do
    begin
      read(ch);
      if length < (maxnamelength - 1) then
      begin
	length:= length + 1;
	filename[length]:= ch
      end
    end;
  readln
end;  { getfilename }

procedure getwhattodo;
{ gets problem data besides specs: whattodo, Lsmallest, Llargest,
  npushed, bandpushed, n. Meant to be interactive, so doesn't abort. }

begin  { getwhattodo }
  gotwhattodo:= true;
  writeln('enter "m" to find minimum length');
  writeln('      "o" to optimize');
  writeln('      "p" to push a band edge');
  readln(ch);
  if( ch = 'm' ) then whattodo:= findlen;
  if( ch = 'o' ) then whattodo:= maxdist;
  if( ch = 'p' ) then whattodo:= pushedge;
  if ( whattodo = findlen ) then
    begin
      writeln;
      writeln('  finding minimum length');
      ok:= false;
      while not ok do
       begin
	writeln('  enter smallest and largest lengths to be considered');
	writeln('  both odd, or both even, between 1 and ', Lmax:3);
	getnum( 2 );
	Lsmallest:= trunc(result[1]);
	Llargest:=  trunc(result[2]);
	if ( (Lsmallest < 1) or (Llargest > Lmax) ) then
	 writeln('Lsmallest < 1 or Llargest > ',
		  Lmax:3, '; please try again')
	  else
	   if odd(Lsmallest)<>odd(Llargest) then
	    writeln('parity of lengths not the same; please try again')
	     else ok:= true
       end
    end;
  if( whattodo = maxdist ) then
    begin
      writeln;
      writeln('  finding solution that maximizes distance from constraints');
      ok:= false;
      while not ok do
       begin
	writeln('  enter (fixed) filter length, between 1 and ', Lmax:3);
	getnum( 1 );
	Lsmallest:= trunc(result[1]);
	Llargest:= Lsmallest;
	if ( (Lsmallest < 1) or (Llargest > Lmax) ) then
	 writeln('length < 1 or length > ',
		  Lmax:3, '; please try again')
	  else ok:= true
       end
    end;
  if ( whattodo = pushedge ) then
    begin
      writeln;
      writeln('  pushing edges');
      ok:= false;
      while not ok do
       begin
	writeln('  enter (fixed) filter length, between 1 and ', Lmax:3);
	getnum( 1 );
	Lsmallest:= trunc(result[1]);
	Llargest:= Lsmallest;
	if ( (Lsmallest < 1) or (Llargest > Lmax) ) then
	 writeln('length < 1 or length > ',
		  Lmax:3, '; please try again')
	  else ok:= true
       end;
      writeln('enter "l" to push left, or "r" to push right');
      readln(ch);
      if( ch = 'l' ) then whichway:= ll else whichway:= rr;
      writeln('enter number of bandedges to be pushed');
      getnum( 1 );
      npushed:= trunc(result[1]);
      writeln('enter list of bandedges to be pushed');
      getnum( npushed );
      for i:= 1 to npushed do  bandpushed[i]:= trunc(result[i])
    end;
  writeln('enter "c" or "s" for cos or sin model (symm. or anti-symm. coeffs.)');
  readln(ch);
  if (ch = 'c') then symtype:= cosine else symtype:= sine;
  writeln('enter number of grid points less 1');
  getnum( 1 );
  n:= trunc(result[1])
end;  { getwhattodo }


procedure print;
{ prints table of specs and whattodo }

begin  { print }
  if( nspec > 0 ) then
    begin
      writeln('  # type  sense  edge1    edge2   bound1   bound2  hugged?  interp');
      for i:= 1 to nspec do
	begin
	  if( spectype[i] = lim ) then
	    writeln(i:3, ' limit   ', sense[i], ' ',
		    left[i]:8:5, ' ', right[i]:8:5, ' ',
		    bound1[i]:8:5, ' ', bound2[i]:8:5, '     ', hug[i],
		    '        ', interpolate[i]);
	  if( spectype[i] = con ) then
	    writeln(i:3, ' convex  ', sense[i], ' ',
		    left[i]:8:5, ' ', right[i]:8:5, ' ')
	end
    end;
  if( gotwhattodo ) then
    begin
      if( whattodo = findlen ) then
       begin
	writeln('    FINDING MIN LENGTH ');
	if odd(Lsmallest)
	 then
	  writeln('    ODD LENGTHS from ', Lsmallest:3, ' to ', Llargest:3)
	 else
	  writeln('    EVEN LENGTHS from ', Lsmallest:3, ' to ', Llargest:3)
       end;
      if( whattodo = maxdist ) then
	writeln('    OPTIMIZING, fixed length= ', Lsmallest:3);
      if( whattodo = pushedge ) then
	begin
	  if( whichway = ll ) then
	    write('PUSHING ', npushed:2, ' BANDEDGES LEFT, fixed length= ',
		  Lsmallest:3);
	  if( whichway = rr ) then
	    write('PUSHING ', npushed:2, ' BANDEDGES RIGHT, fixed length= ',
		  Lsmallest:3);
	  write(', bands: ');
	  for i:= 1 to npushed do write(bandpushed[i]:3);
	  writeln;
	end;
       if (symtype = cosine) then
	writeln('    COSINE model (symmetric coeffs.)')
       else
	writeln('    SINE model (anti-symmetric coeffs.)');
       writeln('  ', (n+1):5, ' grid points')
    end
end;  { print }

procedure delete(k: integer);
{ deletes k-th spec }

begin  { delete }
  for i:= k to (nspec-1) do
    begin
      sense[i]:= sense[i+1];
      left[i]:= left[i+1];
      right[i]:= right[i+1];
      bound1[i]:= bound1[i+1];
      bound2[i]:= bound2[i+1];
      hug[i]:= hug[i+1];
      spectype[i]:= spectype[i+1];
      sense[i]:= sense[i+1];
      left[i]:= left[i+1];
      right[i]:= right[i+1]
    end;
  nspec:= nspec - 1
end;  { delete }

procedure readdata;
{ reads in data from old file }
{ not meant to be interactive, so aborts on bad filter lengths }

begin  { readdata }
  readln(infile, Lsmallest, Llargest);

  readln(infile, ch);
  if (ch = 'c') then symtype:= cosine else symtype:= sine;

  if odd(Lsmallest)<>odd(Llargest) then
   begin
    writeln('parity of lengths not the same in input file: quitting');
    halt
   end;

  if ( (Lsmallest < 1) or (Llargest > Lmax) ) then
   begin
    writeln('filter length out of range: quitting');
    halt
   end;

  if( Lsmallest <> Llargest ) then
   whattodo:= findlen;

  if( Lsmallest = Llargest ) then
    begin
      readln(infile, ch);     { right, left, or neither: edges to be pushed? }
      if( ch = 'n' ) then  whattodo:= maxdist
	else
	  begin
	    whattodo:= pushedge;
	    if( ch = 'r' ) then whichway:= rr else whichway:= ll;
	    readln(infile, npushed);
	    for i:= 1 to npushed do read(infile, bandpushed[i]);
	    readln(infile)
	  end
    end;
  gotwhattodo:= true;
  readln(infile, n);  { there are n+1 grid points between 0 and pi }
  nspec:= 0;
  readln(infile, ch);
  while( ch <> 'e' ) do   { 'e' for end }
    begin
      nspec:= nspec + 1;
      i:= nspec;
      if( ch = 'c') then
	begin
	  spectype[i]:= con;
	  readln( infile, sense[i] );
	  readln( infile, left[i], right[i] )
	end;
      if( ch = 'l') then
	begin
	  spectype[i]:= lim;
	  readln( infile, sense[i] );
	  readln( infile, interpolate[i] );
	  readln( infile, hug[i] );
	  readln( infile, left[i], right[i] );
	  readln( infile, bound1[i], bound2[i] );
	end;
      readln(infile, ch)  { next }
    end  { while }
  end;   { readdata }


begin  { main }
  writeln('WELCOME TO METEOR FORMATTER: GENERATES INPUT FILE FOR METEOR');
  writeln;
  gotwhattodo:= false;
  nspec:= 0;
  writeln('enter "y" if you want to edit an old file');
  readln(ch);
  if( ch = 'y') then
    begin
      writeln('enter name of input file, up to ', maxnamelength:3,
	      ' characters');
      getfilename(infilename);
      writeln('filename: ', infilename);
      reset(infile, infilename);
      readdata;
      print
    end;
  writeln;
  writeln('enter name of output file, up to ', maxnamelength:3, ' characters');
  getfilename(outfilename);
  while( outfilename = infilename ) do
    begin
      writeln('same as infilename, please try again');
      getfilename(outfilename)
    end;
  writeln('filename: ', outfilename);
  rewrite(outfile, outfilename);
  ch:= 'x';
  while( ch <> 'w' ) do
    begin
      writeln(' ');
      writeln('enter "y" to read spec number ', nspec+1:3);
      writeln('      "p" to print current information');
      writeln('      "r" to re-enter a spec');
      writeln('      "d" to delete a spec');
      writeln('      "s" to specify what to do');
      writeln('      "w" to write output file and exit');
      readln(ch);
      if( ch = 'y' ) then
	begin
	  nspec:= nspec + 1;
	  getspec(nspec)
	end;
      if( ch = 'p' ) then print;
      if( ch = 'r' ) then
	begin
	  writeln('enter number of spec you want to re-enter');
	  getnum( 1 );
	  i:= trunc(result[1]);
	  getspec(i)
	end;
      if( ch = 'd') then
	begin
	  writeln('enter number of spec you want to delete');
	  getnum(1);
	  i:= trunc(result[1]);
	  delete(i)
	end;
      if( ch = 's') then getwhattodo;
      if( ch = 'w' ) then
	if( gotwhattodo and ( nspec > 0 ) ) then
	  begin
	    writeln;
	    write('writing file "');
	    for i:= 1 to 10 do
	     if (outfilename[i]<> ' ') then write(outfilename[i]);
	    writeln('" and exiting');
	    writefile
	  end
	else
	  begin
	    if( not gotwhattodo ) then
	      writeln('please specify what to do');
	    if( nspec = 0 ) then
	      writeln('please enter some specs');
	    ch:= 'x'    { don't exit loop }
	  end
    end
end.  { main }



