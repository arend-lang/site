require 'rly'

class ArendLexer < Rly::Lex
  start_char = '~!@#\$%\^&\*\-\+=<>\?/\|\[\]:a-zA-Z_|\u005D\u2200-\u22FF'

  id = "[#{start_char}][#{start_char}0-9']*"

  token(:COMMENT, /\-\- .*|\{-([^-]|-+[^}])*-\}/) do |tok|
    tok.value = "<span class=\'c\'>#{tok.value}</span>"
    tok
  end

  token(:OPERATOR, /(=>|@|==|=|\+|\*|\$)'*|->|:|,|\||`#{id}`?/) do |tok|
    tok.value = "<span class=\'o\'>#{tok.value}</span>"
    tok
  end

  token(:UNKNOWN, /_/) do |tok|
    tok.value = "<span class=\'u\'>#{tok.value}</span>"
    tok
  end

  token(:GOAL, /\{\?(#{id})?\}/) do |tok|
    tok.value = "<span class=\'g\'>#{tok.value}</span>"
    tok
  end

  token(:ID, /#{id}/)

  token(:PROP, /\\Prop/) do |tok|
    tok.value = "<span class=\'kt\'>#{tok.value}</span>"
    tok
  end

  token(:SET, /\\Set[0-9]*/) do |tok|
    tok.value = "<span class=\'kt\'>#{tok.value}</span>"
    tok
  end

  token(:TYPE, /\\([0-9]+-)?Type[0-9]*/) do |tok|
    tok.value = "<span class=\'kt\'>#{tok.value}</span>"
    tok
  end

  token(:KW, /\\[^\s]+/) do |tok|
    tok.value = "<span class=\'k\'>#{tok.value}</span>"
    tok
  end

  token(:NUMBER, /-?[0-9]+/) do |tok|
    tok.value = "<span class=\'n\'>#{tok.value}</span>"
    tok
  end

  token(:ANY, /[ \t\r\n\(\)\.]+/)

  token(:BRACE, /[\{\}]/)

  on_error do |tok|
    puts "Illegal character: #{tok.value} at #{tok.lexer.pos}"
    tok.lexer.pos += 1
    nil
  end
end

class ArendHighlighter < Liquid::Block
  def render(context)
    lexer = ArendLexer.new(super(context).strip)
    s = StringIO.new
    s << "<div class=\'highlighter-rouge\'><div class=\'highlight\'><pre class=\'highlight\'><code>"
    while tok = lexer.next do
      s << tok.value
    end
    s << "</code></pre></div></div>"
    s.string
  end
end

class ArendInlineHighlighter < Liquid::Block
  def render(context)
    lexer = ArendLexer.new(super(context).strip)
    s = StringIO.new
    s << "<span class=\"inl-highlight\">"
    while tok = lexer.next do
      s << tok.value
    end
    s << "</span>"
    s.string
  end
end

Liquid::Template.register_tag("arend", ArendHighlighter)

Liquid::Template.register_tag("ard", ArendInlineHighlighter)
