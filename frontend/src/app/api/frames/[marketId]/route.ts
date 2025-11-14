import { NextRequest, NextResponse } from 'next/server';

export async function GET(
  request: NextRequest,
  { params }: { params: { marketId: string } }
) {
  const marketId = params.marketId;

  // TODO: Fetch market data from contract
  const marketData = {
    name: "Example Market",
    yesPrice: 65,
    noPrice: 35,
  };

  // Return Farcaster Frame HTML
  return new NextResponse(
    `<!DOCTYPE html>
    <html>
      <head>
        <meta property="fc:frame" content="vNext" />
        <meta property="fc:frame:image" content="${process.env.NEXT_PUBLIC_URL}/api/frames/${marketId}/image" />
        <meta property="fc:frame:button:1" content="YES ${marketData.yesPrice}%" />
        <meta property="fc:frame:button:1:action" content="tx" />
        <meta property="fc:frame:button:1:target" content="${process.env.NEXT_PUBLIC_URL}/api/frames/${marketId}/tx/0" />
        <meta property="fc:frame:button:2" content="NO ${marketData.noPrice}%" />
        <meta property="fc:frame:button:2:action" content="tx" />
        <meta property="fc:frame:button:2:target" content="${process.env.NEXT_PUBLIC_URL}/api/frames/${marketId}/tx/1" />
        <meta property="fc:frame:button:3" content="View Market" />
        <meta property="fc:frame:button:3:action" content="link" />
        <meta property="fc:frame:button:3:target" content="${process.env.NEXT_PUBLIC_URL}/market/${marketId}" />
      </head>
      <body>
        <h1>${marketData.name}</h1>
      </body>
    </html>`,
    {
      headers: {
        'Content-Type': 'text/html',
      },
    }
  );
}

export async function POST(
  request: NextRequest,
  { params }: { params: { marketId: string } }
) {
  // Handle Frame interactions
  const body = await request.json();

  // Validate frame signature
  // Process user interaction
  // Return next frame state

  return NextResponse.json({
    // Frame response
  });
}
