
#include <stdio.h>
#include <string.h>
#include <stddef.h>
#include <math.h>
#include <assert.h>
#include "Garbage_collector_for_Dunix.c"
#include "boot.asm"
#define LEN 100 
#ifndef ARRAY_SIZE
#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof(arr[0]))
#endif

#define KSYM_NAME_LEN		128


int time () 
{
	long int ttime;

	ttime=time(NULL); // We  need understand  curently  time 

	printf("Time : %s\n",ctime (&ttime) );

	return 0 ; 
}


// Launcher of the Dunix 

int start () {

     __assembly__ {
       
         section.text
      use16
      org 0x7C00
start:
mov ax, cs
mov ds, ax
mov si,a
cld
mov ah, 0x0e
mov bh,0
jmp puts_loop
puts_loop:
  lodsb
    test al , al
    jz text_
    int 10h
    jmp puts_loop
text_
mov ah,0
int 16h
cmp ah,0Eh
jz text_back
mov ah,0x0e
mov bh,0
int 10h
jmp text_
text_back:
mov ah,0x0e
mov bh,0
mov al,8
int 10h
section .data
a db 'Starting Dunix 1.0 ',0

    }


return 0 ;

}
/* Generate assembler source containing symbol information
 *
 * Copyright 2002       by Kai Germaschewski
 *
 * This software may be used and distributed according to the terms
 * of the GNU General Public License, incorporated herein by reference.
 *
 * Usage: nm -n vmlinux | scripts/kallsyms [--all-symbols] > symbols.S
 *
 *      Table compression uses all the unused char codes on the symbols and
 *  maps these to the most used substrings (tokens). For instance, it might
 *  map char code 0xF7 to represent "write_" and then in every symbol where
 *  "write_" appears it can be replaced by 0xF7, saving 5 bytes.
 *      The used codes themselves are also placed in the table so that the
 *  decompresion can work without "special cases".
 *      Applied to kernel symbols, this usually produces a compression ratio
 *  of about 50%.
 *
 */
struct sym_entry {
	unsigned long long addr;
	unsigned int len;
	unsigned int start_pos;
	unsigned char *sym;
	unsigned int percpu_absolute;
};

struct addr_range {
	const char *start_sym, *end_sym;
	unsigned long long start, end;
};

static unsigned long long _text;
static unsigned long long relative_base;
static struct addr_range text_ranges[] = {
	{ "_stext",     "_etext"     },
	{ "_sinittext", "_einittext" },
};
#define text_range_text     (&text_ranges[0])
#define text_range_inittext (&text_ranges[1])

static struct addr_range percpu_range = {
	"__per_cpu_start", "__per_cpu_end", -1ULL, 0
};

static struct sym_entry *table;
static unsigned int table_size, table_cnt;
static int all_symbols = 0;
static int absolute_percpu = 0;
static int base_relative = 0;

static int token_profit[0x10000];

/* the table that holds the result of the compression */
static unsigned char best_table[256][2];
static unsigned char best_table_len[256];


static void usage(void)
{
	fprintf(stderr, "Usage: kallsyms [--all-symbols] "
			"[--base-relative] < in.map > out.S\n");
	exit(1);
}

/*
 * This ignores the intensely annoying "mapping symbols" found
 * in ARM ELF files: $a, $t and $d.
 */
static int is_arm_mapping_symbol(const char *str)
{
	return str[0] == '$' && strchr("axtd", str[1])
	       && (str[2] == '\0' || str[2] == '.');
}

static int check_symbol_range(const char *sym, unsigned long long addr,
			      struct addr_range *ranges, int entries)
{
	size_t i;
	struct addr_range *ar;

	for (i = 0; i < entries; ++i) {
		ar = &ranges[i];

		if (strcmp(sym, ar->start_sym) == 0) {
			ar->start = addr;
			return 0;
		} else if (strcmp(sym, ar->end_sym) == 0) {
			ar->end = addr;
			return 0;
		}
	}

	return 1;
}

static int read_symbol(FILE *in, struct sym_entry *s)
{
	char sym[500], stype;
	int rc;

	rc = fscanf(in, "%llx %c %499s\n", &s->addr, &stype, sym);
	if (rc != 3) {
		if (rc != EOF && fgets(sym, 500, in) == NULL)
			fprintf(stderr, "Read error or end of file.\n");
		return -1;
	}
	if (strlen(sym) >= KSYM_NAME_LEN) {
		fprintf(stderr, "Symbol %s too long for kallsyms (%zu >= %d).\n"
				"Please increase KSYM_NAME_LEN both in kernel and kallsyms.c\n",
			sym, strlen(sym), KSYM_NAME_LEN);
		return -1;
	}

	/* Ignore most absolute/undefined (?) symbols. */
	if (strcmp(sym, "_text") == 0)
		_text = s->addr;
	else if (check_symbol_range(sym, s->addr, text_ranges,
				    ARRAY_SIZE(text_ranges)) == 0)
		/* nothing to do */;
	else if (toupper(stype) == 'A')
	{
		/* Keep these useful absolute symbols */
		if (strcmp(sym, "__kernel_syscall_via_break") &&
		    strcmp(sym, "__kernel_syscall_via_epc") &&
		    strcmp(sym, "__kernel_sigtramp") &&
		    strcmp(sym, "__gp"))
			return -1;

	}
	else if (toupper(stype) == 'U' ||
		 is_arm_mapping_symbol(sym))
		return -1;
	/* exclude also MIPS ELF local symbols ($L123 instead of .L123) */
	else if (sym[0] == '$')
		return -1;
	/* exclude debugging symbols */
	else if (stype == 'N' || stype == 'n')
		return -1;
	/* exclude s390 kasan local symbols */
	else if (!strncmp(sym, ".LASANPC", 8))
		return -1;

	/* include the type field in the symbol name, so that it gets
	 * compressed together */
	s->len = strlen(sym) + 1;
	s->sym = malloc(s->len + 1);
	if (!s->sym) {
		fprintf(stderr, "kallsyms failure: "
			"unable to allocate required amount of memory\n");
		exit(EXIT_FAILURE);
	}
	strcpy((char *)s->sym + 1, sym);
	s->sym[0] = stype;

	s->percpu_absolute = 0;

	/* Record if we've found __per_cpu_start/end. */
	check_symbol_range(sym, s->addr, &percpu_range, 1);

	return 0;
}

static int symbol_in_range(struct sym_entry *s, struct addr_range *ranges,
			   int entries)
{
	size_t i;
	struct addr_range *ar;

	for (i = 0; i < entries; ++i) {
		ar = &ranges[i];

		if (s->addr >= ar->start && s->addr <= ar->end)
			return 1;
	}

	return 0;
}

static int symbol_valid(struct sym_entry *s)
{
	/* Symbols which vary between passes.  Passes 1 and 2 must have
	 * identical symbol lists.  The kallsyms_* symbols below are only added
	 * after pass 1, they would be included in pass 2 when --all-symbols is
	 * specified so exclude them to get a stable symbol list.
	 */
	static char *special_symbols[] = {
		"kallsyms_addresses",
		"kallsyms_offsets",
		"kallsyms_relative_base",
		"kallsyms_num_syms",
		"kallsyms_names",
		"kallsyms_markers",
		"kallsyms_token_table",
		"kallsyms_token_index",

	/* Exclude linker generated symbols which vary between passes */
		"_SDA_BASE_",		/* ppc */
		"_SDA2_BASE_",		/* ppc */
		NULL };

	static char *special_prefixes[] = {
		"__crc_",		/* modversions */
		"__efistub_",		/* arm64 EFI stub namespace */
		NULL };

	static char *special_suffixes[] = {
		"_veneer",		/* arm */
		"_from_arm",		/* arm */
		"_from_thumb",		/* arm */
		NULL };

	int i;
	char *sym_name = (char *)s->sym + 1;

	/* if --all-symbols is not specified, then symbols outside the text
	 * and inittext sections are discarded */
	if (!all_symbols) {
		if (symbol_in_range(s, text_ranges,
				    ARRAY_SIZE(text_ranges)) == 0)
			return 0;
		/* Corner case.  Discard any symbols with the same value as
		 * _etext _einittext; they can move between pass 1 and 2 when
		 * the kallsyms data are added.  If these symbols move then
		 * they may get dropped in pass 2, which breaks the kallsyms
		 * rules.
		 */
		if ((s->addr == text_range_text->end &&
				strcmp(sym_name,
				       text_range_text->end_sym)) ||
		    (s->addr == text_range_inittext->end &&
				strcmp(sym_name,
				       text_range_inittext->end_sym)))
			return 0;
	}

	/* Exclude symbols which vary between passes. */
	for (i = 0; special_symbols[i]; i++)
		if (strcmp(sym_name, special_symbols[i]) == 0)
			return 0;

	for (i = 0; special_prefixes[i]; i++) {
		int l = strlen(special_prefixes[i]);

		if (l <= strlen(sym_name) &&
		    strncmp(sym_name, special_prefixes[i], l) == 0)
			return 0;
	}

	for (i = 0; special_suffixes[i]; i++) {
		int l = strlen(sym_name) - strlen(special_suffixes[i]);

		if (l >= 0 && strcmp(sym_name + l, special_suffixes[i]) == 0)
			return 0;
	}

	return 1;
}

static void read_map(FILE *in)
{
	while (!feof(in)) {
		if (table_cnt >= table_size) {
			table_size += 10000;
			table = realloc(table, sizeof(*table) * table_size);
			if (!table) {
				fprintf(stderr, "out of memory\n");
				exit (1);
			}
		}
		if (read_symbol(in, &table[table_cnt]) == 0) {
			table[table_cnt].start_pos = table_cnt;
			table_cnt++;
		}
	}
}

static void output_label(char *label)
{
	printf(".globl %s\n", label);
	printf("\tALGN\n");
	printf("%s:\n", label);
}

/* uncompress a compressed symbol. When this function is called, the best table
 * might still be compressed itself, so the function needs to be recursive */
static int expand_symbol(unsigned char *data, int len, char *result)
{
	int c, rlen, total=0;

	while (len) {
		c = *data;
		/* if the table holds a single char that is the same as the one
		 * we are looking for, then end the search */
		if (best_table[c][0]==c && best_table_len[c]==1) {
			*result++ = c;
			total++;
		} else {
			/* if not, recurse and expand */
			rlen = expand_symbol(best_table[c], best_table_len[c], result);
			total += rlen;
			result += rlen;
		}
		data++;
		len--;
	}
	*result=0;

	return total;
}

static int symbol_absolute(struct sym_entry *s)
{
	return s->percpu_absolute;
}

static void write_src(void)
{
	unsigned int i, k, off;
	unsigned int best_idx[256];
	unsigned int *markers;
	char buf[KSYM_NAME_LEN];

	printf("#include <asm/bitsperlong.h>\n");
	printf("#if BITS_PER_LONG == 64\n");
	printf("#define PTR .quad\n");
	printf("#define ALGN .balign 8\n");
	printf("#else\n");
	printf("#define PTR .long\n");
	printf("#define ALGN .balign 4\n");
	printf("#endif\n");

	printf("\t.section .rodata, \"a\"\n");

	/* Provide proper symbols relocatability by their relativeness
	 * to a fixed anchor point in the runtime image, either '_text'
	 * for absolute address tables, in which case the linker will
	 * emit the final addresses at build time. Otherwise, use the
	 * offset relative to the lowest value encountered of all relative
	 * symbols, and emit non-relocatable fixed offsets that will be fixed
	 * up at runtime.
	 *
	 * The symbol names cannot be used to construct normal symbol
	 * references as the list of symbols contains symbols that are
	 * declared static and are private to their .o files.  This prevents
	 * .tmp_kallsyms.o or any other object from referencing them.
	 */
	if (!base_relative)
		output_label("kallsyms_addresses");
	else
		output_label("kallsyms_offsets");

	for (i = 0; i < table_cnt; i++) {
		if (base_relative) {
			long long offset;
			int overflow;

			if (!absolute_percpu) {
				offset = table[i].addr - relative_base;
				overflow = (offset < 0 || offset > UINT_MAX);
			} else if (symbol_absolute(&table[i])) {
				offset = table[i].addr;
				overflow = (offset < 0 || offset > INT_MAX);
			} else {
				offset = relative_base - table[i].addr - 1;
				overflow = (offset < INT_MIN || offset >= 0);
			}
			if (overflow) {
				fprintf(stderr, "kallsyms failure: "
					"%s symbol value %#llx out of range in relative mode\n",
					symbol_absolute(&table[i]) ? "absolute" : "relative",
					table[i].addr);
				exit(EXIT_FAILURE);
			}
			printf("\t.long\t%#x\n", (int)offset);
		} else if (!symbol_absolute(&table[i])) {
			if (_text <= table[i].addr)
				printf("\tPTR\t_text + %#llx\n",
					table[i].addr - _text);
			else
				printf("\tPTR\t_text - %#llx\n",
					_text - table[i].addr);
		} else {
			printf("\tPTR\t%#llx\n", table[i].addr);
		}
	}
	printf("\n");

	if (base_relative) {
		output_label("kallsyms_relative_base");
		printf("\tPTR\t_text - %#llx\n", _text - relative_base);
		printf("\n");
	}

	output_label("kallsyms_num_syms");
	printf("\t.long\t%u\n", table_cnt);
	printf("\n");

	/* table of offset markers, that give the offset in the compressed stream
	 * every 256 symbols */
	markers = malloc(sizeof(unsigned int) * ((table_cnt + 255) / 256));
	if (!markers) {
		fprintf(stderr, "kallsyms failure: "
			"unable to allocate required memory\n");
		exit(EXIT_FAILURE);
	}

	output_label("kallsyms_names");
	off = 0;
	for (i = 0; i < table_cnt; i++) {
		if ((i & 0xFF) == 0)
			markers[i >> 8] = off;

		printf("\t.byte 0x%02x", table[i].len);
		for (k = 0; k < table[i].len; k++)
			printf(", 0x%02x", table[i].sym[k]);
		printf("\n");

		off += table[i].len + 1;
	}
	printf("\n");

	output_label("kallsyms_markers");
	for (i = 0; i < ((table_cnt + 255) >> 8); i++)
		printf("\t.long\t%u\n", markers[i]);
	printf("\n");

	free(markers);

	output_label("kallsyms_token_table");
	off = 0;
	for (i = 0; i < 256; i++) {
		best_idx[i] = off;
		expand_symbol(best_table[i], best_table_len[i], buf);
		printf("\t.asciz\t\"%s\"\n", buf);
		off += strlen(buf) + 1;
	}
	printf("\n");

	output_label("kallsyms_token_index");
	for (i = 0; i < 256; i++)
		printf("\t.short\t%d\n", best_idx[i]);
	printf("\n");
}


/* table lookup compression functions */

/* count all the possible tokens in a symbol */
static void learn_symbol(unsigned char *symbol, int len)
{
	int i;

	for (i = 0; i < len - 1; i++)
		token_profit[ symbol[i] + (symbol[i + 1] << 8) ]++;
}

/* decrease the count for all the possible tokens in a symbol */
static void forget_symbol(unsigned char *symbol, int len)
{
	int i;

	for (i = 0; i < len - 1; i++)
		token_profit[ symbol[i] + (symbol[i + 1] << 8) ]--;
}

/* remove all the invalid symbols from the table and do the initial token count */
static void build_initial_tok_table(void)
{
	unsigned int i, pos;

	pos = 0;
	for (i = 0; i < table_cnt; i++) {
		if ( symbol_valid(&table[i]) ) {
			if (pos != i)
				table[pos] = table[i];
			learn_symbol(table[pos].sym, table[pos].len);
			pos++;
		}
	}
	table_cnt = pos;
}

static void *find_token(unsigned char *str, int len, unsigned char *token)
{
	int i;

	for (i = 0; i < len - 1; i++) {
		if (str[i] == token[0] && str[i+1] == token[1])
			return &str[i];
	}
	return NULL;
}

/* replace a given token in all the valid symbols. Use the sampled symbols
 * to update the counts */
static void compress_symbols(unsigned char *str, int idx)
{
	unsigned int i, len, size;
	unsigned char *p1, *p2;

	for (i = 0; i < table_cnt; i++) {

		len = table[i].len;
		p1 = table[i].sym;

		/* find the token on the symbol */
		p2 = find_token(p1, len, str);
		if (!p2) continue;

		/* decrease the counts for this symbol's tokens */
		forget_symbol(table[i].sym, len);

		size = len;

		do {
			*p2 = idx;
			p2++;
			size -= (p2 - p1);
			memmove(p2, p2 + 1, size);
			p1 = p2;
			len--;

			if (size < 2) break;

			/* find the token on the symbol */
			p2 = find_token(p1, size, str);

		} while (p2);

		table[i].len = len;

		/* increase the counts for this symbol's new tokens */
		learn_symbol(table[i].sym, len);
	}
}

/* search the token with the maximum profit */
static int find_best_token(void)
{
	int i, best, bestprofit;

	bestprofit=-10000;
	best = 0;

	for (i = 0; i < 0x10000; i++) {
		if (token_profit[i] > bestprofit) {
			best = i;
			bestprofit = token_profit[i];
		}
	}
	return best;
}

/* this is the core of the algorithm: calculate the "best" table */
static void optimize_result(void)
{
	int i, best;

	/* using the '\0' symbol last allows compress_symbols to use standard
	 * fast string functions */
	for (i = 255; i >= 0; i--) {

		/* if this table slot is empty (it is not used by an actual
		 * original char code */
		if (!best_table_len[i]) {

			/* find the token with the best profit value */
			best = find_best_token();
			if (token_profit[best] == 0)
				break;

			/* place it in the "best" table */
			best_table_len[i] = 2;
			best_table[i][0] = best & 0xFF;
			best_table[i][1] = (best >> 8) & 0xFF;

			/* replace this token in all the valid symbols */
			compress_symbols(best_table[i], i);
		}
	}
}

/* start by placing the symbols that are actually used on the table */
static void insert_real_symbols_in_table(void)
{
	unsigned int i, j, c;

	for (i = 0; i < table_cnt; i++) {
		for (j = 0; j < table[i].len; j++) {
			c = table[i].sym[j];
			best_table[c][0]=c;
			best_table_len[c]=1;
		}
	}
}

static void optimize_token_table(void)
{
	build_initial_tok_table();

	insert_real_symbols_in_table();

	/* When valid symbol is not registered, exit to error */
	if (!table_cnt) {
		fprintf(stderr, "No valid symbol.\n");
		exit(1);
	}

	optimize_result();
}

/* guess for "linker script provide" symbol */
static int may_be_linker_script_provide_symbol(const struct sym_entry *se)
{
	const char *symbol = (char *)se->sym + 1;
	int len = se->len - 1;

	if (len < 8)
		return 0;

	if (symbol[0] != '_' || symbol[1] != '_')
		return 0;

	/* __start_XXXXX */
	if (!memcmp(symbol + 2, "start_", 6))
		return 1;

	/* __stop_XXXXX */
	if (!memcmp(symbol + 2, "stop_", 5))
		return 1;

	/* __end_XXXXX */
	if (!memcmp(symbol + 2, "end_", 4))
		return 1;

	/* __XXXXX_start */
	if (!memcmp(symbol + len - 6, "_start", 6))
		return 1;

	/* __XXXXX_end */
	if (!memcmp(symbol + len - 4, "_end", 4))
		return 1;

	return 0;
}

static int prefix_underscores_count(const char *str)
{
	const char *tail = str;

	while (*tail == '_')
		tail++;

	return tail - str;
}

static int compare_symbols(const void *a, const void *b)
{
	const struct sym_entry *sa;
	const struct sym_entry *sb;
	int wa, wb;

	sa = a;
	sb = b;

	/* sort by address first */
	if (sa->addr > sb->addr)
		return 1;
	if (sa->addr < sb->addr)
		return -1;

	/* sort by "weakness" type */
	wa = (sa->sym[0] == 'w') || (sa->sym[0] == 'W');
	wb = (sb->sym[0] == 'w') || (sb->sym[0] == 'W');
	if (wa != wb)
		return wa - wb;

	/* sort by "linker script provide" type */
	wa = may_be_linker_script_provide_symbol(sa);
	wb = may_be_linker_script_provide_symbol(sb);
	if (wa != wb)
		return wa - wb;

	/* sort by the number of prefix underscores */
	wa = prefix_underscores_count((const char *)sa->sym + 1);
	wb = prefix_underscores_count((const char *)sb->sym + 1);
	if (wa != wb)
		return wa - wb;

	/* sort by initial order, so that other symbols are left undisturbed */
	return sa->start_pos - sb->start_pos;
}

static void sort_symbols(void)
{
	qsort(table, table_cnt, sizeof(struct sym_entry), compare_symbols);
}

static void make_percpus_absolute(void)
{
	unsigned int i;

	for (i = 0; i < table_cnt; i++)
		if (symbol_in_range(&table[i], &percpu_range, 1)) {
			/*
			 * Keep the 'A' override for percpu symbols to
			 * ensure consistent behavior compared to older
			 * versions of this tool.
			 */
			table[i].sym[0] = 'A';
			table[i].percpu_absolute = 1;
		}
}

/* find the minimum non-absolute symbol address */
static void record_relative_base(void)
{
	unsigned int i;

	relative_base = -1ULL;
	for (i = 0; i < table_cnt; i++)
		if (!symbol_absolute(&table[i]) &&
		    table[i].addr < relative_base)
			relative_base = table[i].addr;
}

int Applied_to_kernel_symbols(int argc, char **argv)
{
	if (argc >= 2) {
		int i;
		for (i = 1; i < argc; i++) {
			if(strcmp(argv[i], "--all-symbols") == 0)
				all_symbols = 1;
			else if (strcmp(argv[i], "--absolute-percpu") == 0)
				absolute_percpu = 1;
			else if (strcmp(argv[i], "--base-relative") == 0)
				base_relative = 1;
			else
				usage();
		}
	} else if (argc != 1)
		usage();

	read_map(stdin);
	if (absolute_percpu)
		make_percpus_absolute();
	if (base_relative)
		record_relative_base();
	sort_symbols();
	optimize_token_table();
	write_src();

	return 0;
}
/*
 * Unloved program to convert a binary on stdin to a C include on stdout
 *
 * Jan 2019 Shishov Michael  <fandim16k@gmail.com>
 */
int convert_to_C(int argc, char *argv[])
{
	int ch, total = 0;

	if (argc > 1)
		printf("const char %s[] %s=\n",
			argv[1], argc > 2 ? argv[2] : "");

	do {
		printf("\t\"");
		while ((ch = getchar()) != EOF) {
			total++;
			printf("\\x%02x", ch);
			if (total % 16 == 0)
				break;
		}
		printf("\"\n");
	} while (ch != EOF);

	if (argc > 1)
		printf("\t;\n\n#include <linux/types.h>\n\nconst size_t %s_size = %d;\n",
		       argv[1], total);

	return 0;
}

int FILE_SYSTEM=[10] {

  Home , Computer,Network, System ,Hardware


};  // Main Folders 


/*
 * Copyright 2012-2016 by the PaX Team <pageexec@freemail.hu>
 * Copyright 2016 by Emese Revfy <re.emese@gmail.com>
 * Licensed under the GPL v2
 *
 * Note: the choice of the license means that the compilation process is
 *       NOT 'eligible' as defined by gcc's library exception to the GPL v3,
 *       but for the kernel it doesn't matter since it doesn't link against
 *       any of the gcc libraries
 *
 * This gcc plugin helps generate a little bit of entropy from program state,
 * used throughout the uptime of the kernel. Here is an instrumentation example:
 *
 * before:
 * void __latent_entropy test(int argc, char *argv[])
 * {
 *	if (argc <= 1)
 *		printf("%s: no command arguments :(\n", *argv);
 *	else
 *		printf("%s: %d command arguments!\n", *argv, args - 1);
 * }
 *
 * after:
 * void __latent_entropy test(int argc, char *argv[])
 * {
 *	// latent_entropy_execute() 1.
 *	unsigned long local_entropy;
 *	// init_local_entropy() 1.
 *	void *local_entropy_frameaddr;
 *	// init_local_entropy() 3.
 *	unsigned long tmp_latent_entropy;
 *
 *	// init_local_entropy() 2.
 *	local_entropy_frameaddr = __builtin_frame_address(0);
 *	local_entropy = (unsigned long) local_entropy_frameaddr;
 *
 *	// init_local_entropy() 4.
 *	tmp_latent_entropy = latent_entropy;
 *	// init_local_entropy() 5.
 *	local_entropy ^= tmp_latent_entropy;
 *
 *	// latent_entropy_execute() 3.
 *	if (argc <= 1) {
 *		// perturb_local_entropy()
 *		local_entropy += 4623067384293424948;
 *		printf("%s: no command arguments :(\n", *argv);
 *		// perturb_local_entropy()
 *	} else {
 *		local_entropy ^= 3896280633962944730;
 *		printf("%s: %d command arguments!\n", *argv, args - 1);
 *	}
 *
 *	// latent_entropy_execute() 4.
 *	tmp_latent_entropy = rol(tmp_latent_entropy, local_entropy);
 *	latent_entropy = tmp_latent_entropy;
 * }
 *
 * TODO:
 * - add ipa pass to identify not explicitly marked candidate functions
 * - mix in more program state (function arguments/return values,
 *   loop variables, etc)
 * - more instrumentation control via attribute parameters
 *
 * BUGS:
 * - none known
 *
 * Options:
 * -fplugin-arg-latent_entropy_plugin-disable
 *
 * Attribute: __attribute__((latent_entropy))
 *  The latent_entropy gcc attribute can be only on functions and variables.
 *  If it is on a function then the plugin will instrument it. If the attribute
 *  is on a variable then the plugin will initialize it with a random value.
 *  The variable must be an integer, an integer array type or a structure
 *  with integer fields.
 */

#include "gcc-common.h"

__visible int plugin_is_GPL_compatible;

static GTY(()) tree latent_entropy_decl;

static struct plugin_info latent_entropy_plugin_info = {
	.version	= "201606141920vanilla",
	.help		= "disable\tturn off latent entropy instrumentation\n",
};

static unsigned HOST_WIDE_INT seed;
/*
 * get_random_seed() (this is a GCC function) generates the seed.
 * This is a simple random generator without any cryptographic security because
 * the entropy doesn't come from here.
 */
static unsigned HOST_WIDE_INT get_random_const(void)
{
	unsigned int i;
	unsigned HOST_WIDE_INT ret = 0;

	for (i = 0; i < 8 * sizeof(ret); i++) {
		ret = (ret << 1) | (seed & 1);
		seed >>= 1;
		if (ret & 1)
			seed ^= 0xD800000000000000ULL;
	}

	return ret;
}

static tree tree_get_random_const(tree type)
{
	unsigned long long mask;

	mask = 1ULL << (TREE_INT_CST_LOW(TYPE_SIZE(type)) - 1);
	mask = 2 * (mask - 1) + 1;

	if (TYPE_UNSIGNED(type))
		return build_int_cstu(type, mask & get_random_const());
	return build_int_cst(type, mask & get_random_const());
}

static tree handle_latent_entropy_attribute(tree *node, tree name,
						tree args __unused,
						int flags __unused,
						bool *no_add_attrs)
{
	tree type;
#if BUILDING_GCC_VERSION <= 4007
	VEC(constructor_elt, gc) *vals;
#else
	vec<constructor_elt, va_gc> *vals;
#endif

	switch (TREE_CODE(*node)) {
	default:
		*no_add_attrs = true;
		error("%qE attribute only applies to functions and variables",
			name);
		break;

	case VAR_DECL:
		if (DECL_INITIAL(*node)) {
			*no_add_attrs = true;
			error("variable %qD with %qE attribute must not be initialized",
				*node, name);
			break;
		}

		if (!TREE_STATIC(*node)) {
			*no_add_attrs = true;
			error("variable %qD with %qE attribute must not be local",
				*node, name);
			break;
		}

		type = TREE_TYPE(*node);
		switch (TREE_CODE(type)) {
		default:
			*no_add_attrs = true;
			error("variable %qD with %qE attribute must be an integer or a fixed length integer array type or a fixed sized structure with integer fields",
				*node, name);
			break;

		case RECORD_TYPE: {
			tree fld, lst = TYPE_FIELDS(type);
			unsigned int nelt = 0;

			for (fld = lst; fld; nelt++, fld = TREE_CHAIN(fld)) {
				tree fieldtype;

				fieldtype = TREE_TYPE(fld);
				if (TREE_CODE(fieldtype) == INTEGER_TYPE)
					continue;

				*no_add_attrs = true;
				error("structure variable %qD with %qE attribute has a non-integer field %qE",
					*node, name, fld);
				break;
			}

			if (fld)
				break;

#if BUILDING_GCC_VERSION <= 4007
			vals = VEC_alloc(constructor_elt, gc, nelt);
#else
			vec_alloc(vals, nelt);
#endif

			for (fld = lst; fld; fld = TREE_CHAIN(fld)) {
				tree random_const, fld_t = TREE_TYPE(fld);

				random_const = tree_get_random_const(fld_t);
				CONSTRUCTOR_APPEND_ELT(vals, fld, random_const);
			}

			/* Initialize the fields with random constants */
			DECL_INITIAL(*node) = build_constructor(type, vals);
			break;
		}

		/* Initialize the variable with a random constant */
		case INTEGER_TYPE:
			DECL_INITIAL(*node) = tree_get_random_const(type);
			break;

		case ARRAY_TYPE: {
			tree elt_type, array_size, elt_size;
			unsigned int i, nelt;
			HOST_WIDE_INT array_size_int, elt_size_int;

			elt_type = TREE_TYPE(type);
			elt_size = TYPE_SIZE_UNIT(TREE_TYPE(type));
			array_size = TYPE_SIZE_UNIT(type);

			if (TREE_CODE(elt_type) != INTEGER_TYPE || !array_size
				|| TREE_CODE(array_size) != INTEGER_CST) {
				*no_add_attrs = true;
				error("array variable %qD with %qE attribute must be a fixed length integer array type",
					*node, name);
				break;
			}

			array_size_int = TREE_INT_CST_LOW(array_size);
			elt_size_int = TREE_INT_CST_LOW(elt_size);
			nelt = array_size_int / elt_size_int;

#if BUILDING_GCC_VERSION <= 4007
			vals = VEC_alloc(constructor_elt, gc, nelt);
#else
			vec_alloc(vals, nelt);
#endif

			for (i = 0; i < nelt; i++) {
				tree cst = size_int(i);
				tree rand_cst = tree_get_random_const(elt_type);

				CONSTRUCTOR_APPEND_ELT(vals, cst, rand_cst);
			}

			/*
			 * Initialize the elements of the array with random
			 * constants
			 */
			DECL_INITIAL(*node) = build_constructor(type, vals);
			break;
		}
		}
		break;

	case FUNCTION_DECL:
		break;
	}

	return NULL_TREE;
}

static struct attribute_spec latent_entropy_attr = { };

static void register_attributes(void *event_data __unused, void *data __unused)
{
	latent_entropy_attr.name		= "latent_entropy";
	latent_entropy_attr.decl_required	= true;
	latent_entropy_attr.handler		= handle_latent_entropy_attribute;

	register_attribute(&latent_entropy_attr);
}

static bool latent_entropy_gate(void)
{
	tree list;

	/* don't bother with noreturn functions for now */
	if (TREE_THIS_VOLATILE(current_function_decl))
		return false;

	/* gcc-4.5 doesn't discover some trivial noreturn functions */
	if (EDGE_COUNT(EXIT_BLOCK_PTR_FOR_FN(cfun)->preds) == 0)
		return false;

	list = DECL_ATTRIBUTES(current_function_decl);
	return lookup_attribute("latent_entropy", list) != NULL_TREE;
}

static tree create_var(tree type, const char *name)
{
	tree var;

	var = create_tmp_var(type, name);
	add_referenced_var(var);
	mark_sym_for_renaming(var);
	return var;
}

/*
 * Set up the next operation and its constant operand to use in the latent
 * entropy PRNG. When RHS is specified, the request is for perturbing the
 * local latent entropy variable, otherwise it is for perturbing the global
 * latent entropy variable where the two operands are already given by the
 * local and global latent entropy variables themselves.
 *
 * The operation is one of add/xor/rol when instrumenting the local entropy
 * variable and one of add/xor when perturbing the global entropy variable.
 * Rotation is not used for the latter case because it would transmit less
 * entropy to the global variable than the other two operations.
 */
static enum tree_code get_op(tree *rhs)
{
	static enum tree_code op;
	unsigned HOST_WIDE_INT random_const;

	random_const = get_random_const();

	switch (op) {
	case BIT_XOR_EXPR:
		op = PLUS_EXPR;
		break;

	case PLUS_EXPR:
		if (rhs) {
			op = LROTATE_EXPR;
			/*
			 * This code limits the value of random_const to
			 * the size of a long for the rotation
			 */
			random_const %= TYPE_PRECISION(long_unsigned_type_node);
			break;
		}

	case LROTATE_EXPR:
	default:
		op = BIT_XOR_EXPR;
		break;
	}
	if (rhs)
		*rhs = build_int_cstu(long_unsigned_type_node, random_const);
	return op;
}

static gimple create_assign(enum tree_code code, tree lhs, tree op1,
				tree op2)
{
	return gimple_build_assign_with_ops(code, lhs, op1, op2);
}

static void perturb_local_entropy(basic_block bb, tree local_entropy)
{
	gimple_stmt_iterator gsi;
	gimple assign;
	tree rhs;
	enum tree_code op;

	op = get_op(&rhs);
	assign = create_assign(op, local_entropy, local_entropy, rhs);
	gsi = gsi_after_labels(bb);
	gsi_insert_before(&gsi, assign, GSI_NEW_STMT);
	update_stmt(assign);
}

static void __perturb_latent_entropy(gimple_stmt_iterator *gsi,
					tree local_entropy)
{
	gimple assign;
	tree temp;
	enum tree_code op;

	/* 1. create temporary copy of latent_entropy */
	temp = create_var(long_unsigned_type_node, "temp_latent_entropy");

	/* 2. read... */
	add_referenced_var(latent_entropy_decl);
	mark_sym_for_renaming(latent_entropy_decl);
	assign = gimple_build_assign(temp, latent_entropy_decl);
	gsi_insert_before(gsi, assign, GSI_NEW_STMT);
	update_stmt(assign);

	/* 3. ...modify... */
	op = get_op(NULL);
	assign = create_assign(op, temp, temp, local_entropy);
	gsi_insert_after(gsi, assign, GSI_NEW_STMT);
	update_stmt(assign);

	/* 4. ...write latent_entropy */
	assign = gimple_build_assign(latent_entropy_decl, temp);
	gsi_insert_after(gsi, assign, GSI_NEW_STMT);
	update_stmt(assign);
}

static bool handle_tail_calls(basic_block bb, tree local_entropy)
{
	gimple_stmt_iterator gsi;

	for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)) {
		gcall *call;
		gimple stmt = gsi_stmt(gsi);

		if (!is_gimple_call(stmt))
			continue;

		call = as_a_gcall(stmt);
		if (!gimple_call_tail_p(call))
			continue;

		__perturb_latent_entropy(&gsi, local_entropy);
		return true;
	}

	return false;
}

static void perturb_latent_entropy(tree local_entropy)
{
	edge_iterator ei;
	edge e, last_bb_e;
	basic_block last_bb;

	gcc_assert(single_pred_p(EXIT_BLOCK_PTR_FOR_FN(cfun)));
	last_bb_e = single_pred_edge(EXIT_BLOCK_PTR_FOR_FN(cfun));

	FOR_EACH_EDGE(e, ei, last_bb_e->src->preds) {
		if (ENTRY_BLOCK_PTR_FOR_FN(cfun) == e->src)
			continue;
		if (EXIT_BLOCK_PTR_FOR_FN(cfun) == e->src)
			continue;

		handle_tail_calls(e->src, local_entropy);
	}

	last_bb = single_pred(EXIT_BLOCK_PTR_FOR_FN(cfun));
	if (!handle_tail_calls(last_bb, local_entropy)) {
		gimple_stmt_iterator gsi = gsi_last_bb(last_bb);

		__perturb_latent_entropy(&gsi, local_entropy);
	}
}

static void init_local_entropy(basic_block bb, tree local_entropy)
{
	gimple assign, call;
	tree frame_addr, rand_const, tmp, fndecl, udi_frame_addr;
	enum tree_code op;
	unsigned HOST_WIDE_INT rand_cst;
	gimple_stmt_iterator gsi = gsi_after_labels(bb);

	/* 1. create local_entropy_frameaddr */
	frame_addr = create_var(ptr_type_node, "local_entropy_frameaddr");

	/* 2. local_entropy_frameaddr = __builtin_frame_address() */
	fndecl = builtin_decl_implicit(BUILT_IN_FRAME_ADDRESS);
	call = gimple_build_call(fndecl, 1, integer_zero_node);
	gimple_call_set_lhs(call, frame_addr);
	gsi_insert_before(&gsi, call, GSI_NEW_STMT);
	update_stmt(call);

	udi_frame_addr = fold_convert(long_unsigned_type_node, frame_addr);
	assign = gimple_build_assign(local_entropy, udi_frame_addr);
	gsi_insert_after(&gsi, assign, GSI_NEW_STMT);
	update_stmt(assign);

	/* 3. create temporary copy of latent_entropy */
	tmp = create_var(long_unsigned_type_node, "temp_latent_entropy");

	/* 4. read the global entropy variable into local entropy */
	add_referenced_var(latent_entropy_decl);
	mark_sym_for_renaming(latent_entropy_decl);
	assign = gimple_build_assign(tmp, latent_entropy_decl);
	gsi_insert_after(&gsi, assign, GSI_NEW_STMT);
	update_stmt(assign);

	/* 5. mix local_entropy_frameaddr into local entropy */
	assign = create_assign(BIT_XOR_EXPR, local_entropy, local_entropy, tmp);
	gsi_insert_after(&gsi, assign, GSI_NEW_STMT);
	update_stmt(assign);

	rand_cst = get_random_const();
	rand_const = build_int_cstu(long_unsigned_type_node, rand_cst);
	op = get_op(NULL);
	assign = create_assign(op, local_entropy, local_entropy, rand_const);
	gsi_insert_after(&gsi, assign, GSI_NEW_STMT);
	update_stmt(assign);
}

static bool create_latent_entropy_decl(void)
{
	varpool_node_ptr node;

	if (latent_entropy_decl != NULL_TREE)
		return true;

	FOR_EACH_VARIABLE(node) {
		tree name, var = NODE_DECL(node);

		if (DECL_NAME_LENGTH(var) < sizeof("latent_entropy") - 1)
			continue;

		name = DECL_NAME(var);
		if (strcmp(IDENTIFIER_POINTER(name), "latent_entropy"))
			continue;

		latent_entropy_decl = var;
		break;
	}

	return latent_entropy_decl != NULL_TREE;
}

static unsigned int latent_entropy_execute(void)
{
	basic_block bb;
	tree local_entropy;

	if (!create_latent_entropy_decl())
		return 0;

	/* prepare for step 2 below */
	gcc_assert(single_succ_p(ENTRY_BLOCK_PTR_FOR_FN(cfun)));
	bb = single_succ(ENTRY_BLOCK_PTR_FOR_FN(cfun));
	if (!single_pred_p(bb)) {
		split_edge(single_succ_edge(ENTRY_BLOCK_PTR_FOR_FN(cfun)));
		gcc_assert(single_succ_p(ENTRY_BLOCK_PTR_FOR_FN(cfun)));
		bb = single_succ(ENTRY_BLOCK_PTR_FOR_FN(cfun));
	}

	/* 1. create the local entropy variable */
	local_entropy = create_var(long_unsigned_type_node, "local_entropy");

	/* 2. initialize the local entropy variable */
	init_local_entropy(bb, local_entropy);

	bb = bb->next_bb;

	/*
	 * 3. instrument each BB with an operation on the
	 *    local entropy variable
	 */
	while (bb != EXIT_BLOCK_PTR_FOR_FN(cfun)) {
		perturb_local_entropy(bb, local_entropy);
		bb = bb->next_bb;
	};

	/* 4. mix local entropy into the global entropy variable */
	perturb_latent_entropy(local_entropy);
	return 0;
}

static void latent_entropy_start_unit(void *gcc_data __unused,
					void *user_data __unused)
{
	tree type, id;
	int quals;

	seed = get_random_seed(false);

	if (in_lto_p)
		return;

	/* extern volatile unsigned long latent_entropy */
	quals = TYPE_QUALS(long_unsigned_type_node) | TYPE_QUAL_VOLATILE;
	type = build_qualified_type(long_unsigned_type_node, quals);
	id = get_identifier("latent_entropy");
	latent_entropy_decl = build_decl(UNKNOWN_LOCATION, VAR_DECL, id, type);

	TREE_STATIC(latent_entropy_decl) = 1;
	TREE_PUBLIC(latent_entropy_decl) = 1;
	TREE_USED(latent_entropy_decl) = 1;
	DECL_PRESERVE_P(latent_entropy_decl) = 1;
	TREE_THIS_VOLATILE(latent_entropy_decl) = 1;
	DECL_EXTERNAL(latent_entropy_decl) = 1;
	DECL_ARTIFICIAL(latent_entropy_decl) = 1;
	lang_hooks.decls.pushdecl(latent_entropy_decl);
}

#define PASS_NAME latent_entropy
#define PROPERTIES_REQUIRED PROP_gimple_leh | PROP_cfg
#define TODO_FLAGS_FINISH TODO_verify_ssa | TODO_verify_stmts | TODO_dump_func \
	| TODO_update_ssa
#include "gcc-generate-gimple-pass.h"

__visible int plugin_init(struct plugin_name_args *plugin_info,
			  struct plugin_gcc_version *version)
{
	bool enabled = true;
	const char * const plugin_name = plugin_info->base_name;
	const int argc = plugin_info->argc;
	const struct plugin_argument * const argv = plugin_info->argv;
	int i;

	static const struct ggc_root_tab gt_ggc_r_gt_latent_entropy[] = {
		{
			.base = &latent_entropy_decl,
			.nelt = 1,
			.stride = sizeof(latent_entropy_decl),
			.cb = &gt_ggc_mx_tree_node,
			.pchw = &gt_pch_nx_tree_node
		},
		LAST_GGC_ROOT_TAB
	};

	PASS_INFO(latent_entropy, "optimized", 1, PASS_POS_INSERT_BEFORE);

	if (!plugin_default_version_check(version, &gcc_version)) {
		error(G_("incompatible gcc/plugin versions"));
		return 1;
	}

	for (i = 0; i < argc; ++i) {
		if (!(strcmp(argv[i].key, "disable"))) {
			enabled = false;
			continue;
		}
		error(G_("unknown option '-fplugin-arg-%s-%s'"), plugin_name, argv[i].key);
	}

	register_callback(plugin_name, PLUGIN_INFO, NULL,
				&latent_entropy_plugin_info);
	if (enabled) {
		register_callback(plugin_name, PLUGIN_START_UNIT,
					&latent_entropy_start_unit, NULL);
		register_callback(plugin_name, PLUGIN_REGISTER_GGC_ROOTS,
				  NULL, (void *)&gt_ggc_r_gt_latent_entropy);
		register_callback(plugin_name, PLUGIN_PASS_MANAGER_SETUP, NULL,
					&latent_entropy_pass_info);
	}
	register_callback(plugin_name, PLUGIN_ATTRIBUTES, register_attributes,
				NULL);

	return 0;
}



int Delelate_of_File () {

void delete(!= "Home" , "Computer" , "Network ", "System" , "Hardware");





}



int creating_file_txt_for_reading_and_writting( ) {

 char str[LEN];

 FILE *file_ptr;

 file_ptr = fopen("new_file.txt"  , "r+a")

 // r is  read  ,  w is write   ,  a is  adding  the  text  in  the our file , r+ 

  if (file_ptr != NULL) {
  	printf(" File : new is  created seccessufully   \n");
    while (fgets(str ,LEN  , file_ptr  )); // we get data  drom the file 
    fprintf(stdout , "%s\n" , str ) ; 
    printf("Reading is over "); 

    }  
  else 
  {
  	fprintf(stderr ,"File dosen't create s\n");

  	return 1 ; 
  }

}


int Write_down_text_in_file () 
{
	// We add oportunity for  writting in Russian 



	// indexly variable and amount of  the lines

	int k,n = 10 ;

	// Array from symbols

	char txt[1000];

	// Pointer to file 

	FILE *f=fopen("MyFile.txt" , "w" );

	//If you  could open file 

	if(f) 
	{
	
		printf("Enter %d amount lines of the text .\n" , n );

		// Enter text in one line 

    for (k=1 , k<=n, k++)
    { 
    	// Output number of line 

    	printf("%d",k  );

    	// Read text written by keyboard 

    	gets (txt) ;

    	// Record of the text into file 

    	fputs (txt , f); 
   

         }

      }
 // If file doesn't order
    else {
      puts ("File doesn't open ")
    }

    system ("pause>null");

    return 0 ; 

}

int Output_of_file () {


}


/*Processes in Dunix  */

int  list_for_each(list ,&current ->children) {
   
   task =list_entry(list, struct task_struct ,sibling);
   
    /* Variable " task " points at one of processes  strated by  present processes   */
}

struct  task_struct *task;
int  for_each_processes (task) {

   /*For each task  just input his name and PID */
  
     printk("%s[%d]\n" , task ->comm ,task->pid);



} 



char create_katalog_HOME()

{
int  array_binary_code_for_HOME[3342525626]={""};  /*We created arrayies for  writing down  binary  code  */


}

char create_katalog_Network()
{
int  array_binary_code_for_Network[3342525626]={""};

}

char create_katalog_Hardware()
{ 
   
 int  array_binary_code_for_Hardware[3342525626]={""};
  


}

int  main( )
{ 
 
/*Processes in Dunix  */

struct  task_struct *task;
struct  list_head   *list;

    system ( "chcp 1251>null");

int Applied_to_kernel_symbols();
  
int start () ;

	/* code */

	int time ();
	return 0;

