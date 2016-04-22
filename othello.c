/* othello.c 	Tom Weatherhead		Started in 1992
 *
 * This program implements the game of othello, using the minimax algorithm
 * (with alpha-beta pruning) to choose the computer's moves.
 * The "verbose" option is useful for quickly debugging program semantics.
 * (H)elp and (Q)uit are available at the command line.
 * The best_move() function returns a linked list of best move records,
 * to the depth specified by max_ply.  An application heap (manifested as
 * a linked list) stores allocated but currently unused move records
 * in an attempt to reduce the overhead of frequently callng malloc().
 * The board array, the application heap, and the data record for each
 * player could easily be made into C++ objects.
 * The stdio-based I/O lends itself well to portability; this program
 * has been compiled and run under UNIX, VAX/VMS, and Windows.
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include <ctype.h>


/* Constants */

#define BOARD_SIZE	8
#define NUM_VECTORS	8
#define MAX_CHANGES	4*(BOARD_SIZE-3)
#define BOARD_AREA	(BOARD_SIZE*BOARD_SIZE)
#define MAX_NUM_MOVES	BOARD_AREA-4

/* INIT_MAX_EFFECT should be less than the sum of the values of
 * the heuristic function for all board squares.
 */
#define INIT_MAX_EFFECT	-9*BOARD_AREA

/* Heuristic function */
#define idx_weight(x)	((x==0||x==BOARD_SIZE-1)?BOARD_SIZE:1)
#define h_func(r,c)	(idx_weight(r)*idx_weight(c))

/* Define a boolean type */

#ifndef FALSE
#ifdef TRUE
#undef TRUE
#endif
typedef enum { FALSE, TRUE } bool;
#else
#ifndef TRUE
#define TRUE 1
#endif
typedef char bool;
#endif


/* Other type definitions */

typedef enum {
	PT_COMP,
	PT_HUMAN
} player_type_type;

typedef struct {
	int drow, dcol;
} vector_type;

typedef struct coord_struct {
	unsigned int r, c;
	/* "tail" is a pointer to the "next" pointer of the last element
	 * in the list.  This allows constant-time list splicing.
	 */
	struct coord_struct * next, ** tail;
} coord_type;

typedef struct player_data_struct {
	char marker;
	unsigned int count;		/* The number of its markers on the board */
	player_type_type type;
	struct player_data_struct * opponent;
} player_data_type;


/* Global variables
 * These could be moved into a structure, the pointer to which could be
 * passed as a parameter to the appropriate functions.
 */

char board[BOARD_SIZE][BOARD_SIZE + 1];
bool verbose;
coord_type * local_heap = NULL;


/* Add a list of move records to the application heap */

static void enqueue( coord_type * ptr )
{
	if( ptr == NULL ) return;

	*(ptr->tail) = local_heap;
#if 0
	/* Not essential */
	ptr->tail = &local_heap->tail; /* Keeps heap linked to its tail */
#endif
	local_heap = ptr;
} /* enqueue() */


/* Get a blank move record, from the application heap or the real one */

static coord_type * dequeue( void )
{
	coord_type * rtn;

	if( local_heap == NULL ) {
		return( (coord_type *)malloc( sizeof( coord_type ) ) );
	} /* if */

	rtn = local_heap;
	local_heap = local_heap->next;
	return( rtn );
} /* dequeue() */


/* Initialize a player's record.
 * This would make a wonderful constructor in C++
 */

static void set_player_data( player_data_type * player )
{
	char str[10];

	/* Marker must already be set */

	do {
		printf( "%c: (h)uman or (c)omputer: ", player->marker );
		scanf( "%s", str );
	} while( str[0] != 'h'  &&  str[0] != 'c' );

	player->type = ( str[0] == 'h' ) ? PT_HUMAN : PT_COMP;
} /* set_player_data() */


/* Crude but highly portable output */

static void draw_board( void )
{
	unsigned int row;

	printf( "\n       01234567\n" );
	printf( "      +--------+\n" );

	for( row = 0; row < BOARD_SIZE; row++ ) {
		printf( "    %1d |%s|\n", row, board[row] );
	} /* for */

	printf( "      +--------+\n\n\n" );
} /* draw_board() */


/* Using a heuristic, compute the gain resulting from a player's move. */

static unsigned int compute_effect( unsigned int row, unsigned int col,
	player_data_type * player,
	char * changes[MAX_CHANGES], unsigned int * num_changedP )
{
	char * line_change[BOARD_SIZE-1];
	unsigned int row2, col2, num_changed = 0, i, heur_total=0, line_heur_total,
		len, drow, dcol, j;
	static vector_type vector[NUM_VECTORS] = { {-1,-1}, {-1,0}, {-1,1}, {0,-1},
											   {0,1}, {1,-1}, {1,0}, {1,1} };

	for( i = 0; i < NUM_VECTORS; i++ ) {
		len = line_heur_total = 0;
		row2 = row;
		col2 = col;
		drow = vector[i].drow;
		dcol = vector[i].dcol;

		for( ; ; ) {
			row2 += drow;
			col2 += dcol;

			if( row2 >= BOARD_SIZE  ||  col2 >= BOARD_SIZE
				||  board[row2][col2] == ' ' ) {

				len = 0;
				break;
			} else if( board[row2][col2] == player->marker ) break;

			line_heur_total += h_func(row2,col2);
			assert( len < BOARD_SIZE - 1 );
			line_change[len++] = &board[row2][col2];
		} /* for */

		if( len > 0 ) {

			for( j = 0; j < len; j++ ) {
				*(line_change[j]) = player->marker;
			} /* for */

			assert( num_changed + len <= MAX_CHANGES );
			memcpy( &changes[num_changed], line_change, len * sizeof(char *) );
			num_changed += len;
			heur_total += line_heur_total;
		} /* if */
	} /* for */

	if( num_changed > 0 ) {
		heur_total += h_func(row,col);
		board[row][col] = player->marker;	/* Place marker now */
		player->count += num_changed + 1;
		player->opponent->count -= num_changed;
	} /* if */

	if( num_changedP != NULL ) {
		*num_changedP = num_changed;
	} /* if */

	return( heur_total );
} /* compute_effect() */


/* Compute the best-move chain (according to the minimax algorithm)
 */

static int best_move( coord_type ** rtn_chain,
	player_data_type * player,
	unsigned int ply, unsigned int max_ply, int prev_move_val, int best_sibling )
{
	bool done = FALSE;
	char * changes[MAX_CHANGES];
	int effect, max_effect = INIT_MAX_EFFECT;
	unsigned int num_changes, i, j, k, num_best_moves = 0, chosen_move;
	coord_type * best_moves[MAX_NUM_MOVES], * chain_ptr = NULL, * move_ptr;

	for( i = 0; i < BOARD_SIZE  &&  !done; i++ ) {

		for( j = 0; j < BOARD_SIZE  &&  !done; j++ ) {

			if( board[i][j] != ' ' ) continue;

			/* Make and record changes */
			effect = compute_effect( i, j, player, changes, &num_changes );

			if( num_changes == 0 ) continue;

			if( verbose ) {
				printf( "Ply %d: %c placed at (%d,%d)\n", ply, player->marker,
					i, j );
			} /* if */

			if( ply < max_ply  &&
				player->count + player->opponent->count < BOARD_AREA ) {

				effect -= best_move( &chain_ptr, player->opponent,
					ply + 1, max_ply, effect, max_effect );

				/* Insure that no moves are incorrectly ignored */
				assert( effect > INIT_MAX_EFFECT );
			} /* if */

			if( effect > max_effect ) {

				for( k = 0; k < num_best_moves; k++ ) {
					enqueue( best_moves[k] ); /* Enqueue old best chains */
				} /* for */

				if( ply > 1  &&  prev_move_val - effect < best_sibling ) {
					/* Alpha-beta pruning is done here */

					if( verbose ) {
						printf( "prune: %d - %d < %d\n", prev_move_val, effect,
							best_sibling );
					} /* if */

					done = TRUE;
				} /* if */

				max_effect = effect;
				num_best_moves = 0;
			} /* if */

			if( effect == max_effect ) {
				move_ptr = dequeue();
				move_ptr->r = i;
				move_ptr->c = j;
				move_ptr->next = chain_ptr;
				move_ptr->tail = (chain_ptr != NULL) ? chain_ptr->tail
					: &move_ptr->next;
				best_moves[num_best_moves++] = move_ptr;
			} else {
				enqueue( chain_ptr );	/* Return chain to heap */
			} /* if */

			/* Remove marker and undo changes */

			board[i][j] = ' ';
			player->count -= num_changes + 1;
			player->opponent->count += num_changes;

			for( k = 0; k < num_changes; k++ ) {
				*(changes[k]) = player->opponent->marker;
			} /* for */
		} /* for j */
	} /* for i */

	if( rtn_chain == NULL ) {
		/* Do nothing; don't retrieve best-move chain */
	} else if( num_best_moves == 0 ) {
		printf( "Ply %d: no best move chosen\n", ply );
		*rtn_chain = NULL;
		max_effect = 0;
	} else {
		chosen_move = rand() % num_best_moves;
		*rtn_chain = best_moves[chosen_move];

		for( i = 0; i < num_best_moves; i++ ) { /* Free other chains */

			if( i != chosen_move ) {
				enqueue( best_moves[i] );
			} /* if */
		} /* if */

		if( verbose ) {
			printf( "Chose move %d of %d\n", chosen_move, num_best_moves );
			printf( "Ply %d: %c @ (%d,%d) => %d\n", ply, player->marker,
				(*rtn_chain)->r, (*rtn_chain)->c, max_effect );
		} /* if */
	} /* if */

	return( max_effect );
} /* best_move() */


unsigned int main( void )
{
	bool can_go = TRUE, prev_can_go, done = FALSE, pause_after;
	char * changes[MAX_CHANGES], str[10];
	int effect;
	unsigned int i, row, col, num_changed, max_ply;
	player_data_type x_data, o_data, * player, * player_ptr;
	coord_type * chain_ptr, * move_ptr;

	printf( "verbose? " );
	scanf( "%s", str );
	verbose = (str[0] == 'y') ? TRUE : FALSE;

	do {
		printf( "Enter skill level (1-10): " );
		scanf( "%d", &max_ply );
	} while( max_ply < 1  ||  max_ply > 10 );

	x_data.marker = 'X';
	o_data.marker = 'O';
	x_data.opponent = &o_data;
	o_data.opponent = &x_data;
	set_player_data( &x_data );
	set_player_data( &o_data );

	printf( "Pause after computer move? : " );
	scanf( "%s", str );
	pause_after = (str[0] == 'n') ? FALSE : TRUE;

	for( i = 0; i < BOARD_SIZE; i++ ) {
		memset( board[i], ' ', BOARD_SIZE );
		board[i][BOARD_SIZE] = '\0';
	} /* for */

	board[3][3] = board[4][4] = x_data.marker;
	board[3][4] = board[4][3] = o_data.marker;
	x_data.count = o_data.count = 2;

	player = &x_data;
	draw_board();

	printf( "Enter: row, column (comma-separated) (both in range 0-%d)\n",
		BOARD_SIZE-1 );

	do {
		prev_can_go = can_go;
		printf( "Checking viability...\n" );
		can_go = ( best_move( &chain_ptr, player, 1, 1, 0, 0 )
			> 0 ) ? TRUE : FALSE;

		if( !can_go ) {
			printf( "%c cannot move\n", player->marker );

			if( !prev_can_go ) {
				printf( "Deadlock: game terminated\n" );
				break;
			}

		} else if( player->type == PT_HUMAN ) {	/* Player's move */
			printf( "X: %d;  O: %d\n", x_data.count, o_data.count );

			for( ; ; ) {
				printf( "%c: ", player->marker );

				do {
					gets( str );
				} while( str[0] == '\0' );

				if( toupper(str[0]) == 'Q' ) {
					done = TRUE;
					break;
				} else if( toupper(str[0]) == 'H' ) {
					/* Computer finds player's best move */
					effect = best_move( &chain_ptr, player, 1, max_ply,0,0 );
					printf( "Suggest (%d,%d) with an effect of %d\n\n",
					chain_ptr->r, chain_ptr->c, effect );
					enqueue( chain_ptr );
					continue;
				} /* if */

				sscanf( str, "%d,%d", &row, &col );

				if( row >= BOARD_SIZE  ||  col >= BOARD_SIZE ) {
					printf( "Invalid coordinates; re-enter:\n" );
					continue;
				} /* if */

				if( board[row][col] != ' ' ) {
					printf("That position already occupied; try again:\n");
				} else {
					effect = compute_effect( row, col, player, changes, NULL );

					if( effect == 0 ) { /* heur==0 => #ch'd == 0 */
						printf( "Zero-yield move; try again:\n" );
					} else break;		/* Move is OK */
				} /* if */
			} /* for */

			if( done ) break;

		} else {	/* Computer's move */
			printf( "Computer is moving...\n" );
			srand( time( NULL ) );
			effect = best_move( &chain_ptr, player, 1, max_ply, 0, 0 );
			printf( "Computer's move: %c placed at %d, %d\n",
				player->marker, chain_ptr->r, chain_ptr->c );
			compute_effect( chain_ptr->r, chain_ptr->c, player, changes, NULL);

			printf( "Optimal chain:\n" );

			for( move_ptr = chain_ptr, player_ptr = player; move_ptr != NULL;
				move_ptr = move_ptr->next, player_ptr = player_ptr->opponent ) {

				printf( "%c: (%d,%d)\n", player_ptr->marker, move_ptr->r,
					move_ptr->c );
			} /* for */

			enqueue( chain_ptr ); /* Reuse the chain of move records */
		} /* if */

		printf( "\nEffect of move == %d\n", effect );

		if( pause_after  &&  player->type == PT_COMP ) {
			printf( "\nPress RETURN to continue...\n" );
			fflush( stdin );
			getchar();
		} /* if */

		printf( "X: %d;  O: %d\n", x_data.count, o_data.count );
		draw_board();

		player = player->opponent;
	} while( x_data.count > 0  &&  o_data.count > 0
		&&  x_data.count + o_data.count < BOARD_AREA );

	/* Free local heap */

	for( i = 0; local_heap != NULL; i++ ) {
		chain_ptr = local_heap->next;
		free( local_heap );
		local_heap = chain_ptr;
	} /* for */

	printf( "%d objects were in application heap\n", i );
	return( 1 /* May be system-dependent */ );
} /* main() */
